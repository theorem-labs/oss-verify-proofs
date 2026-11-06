(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import ExitSim PropExec CatSim.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__ErrEscape () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.EquivalenceDefinition.Equivalence."; "LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.OmniRun."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.StackLayout."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.DecodeC."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "stdpp.bitvector.definitions."], [["1None"; "1Some"; "1bool"; "1false"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2and"; "2eq"; "2not"; "3N"; "3Z"; "4equiv"]; ["4modeled"; "5omni_equiv"; "5omni_strong_equiv"; "6Image"; "6PhdrInfo"; "6Segment"; "6mkImage"; "7OError"; "7coexec"; "7covered"; "7errors"; "7exec"; "7exits_with"; "7never_errors"; "7omni_corun"; "7omni_run"]; ["7outcome"; "7post"; "8MachineFault"; "8MachineOk"; "8fetch_word"; "8is_ecall"; "8machine_result"; "8machine_state"; "8ms_svc_pending"; "8step"; "9ExecEntry"; "9SNext"; "9all_traces_error"; "9behavior"; "9config"; "9init_machine_state"]; ["9mkCfg"; "9mkEntry"; "9reaches_error"; "9reaches_unmodeled"; "9run"; "9sstep"; "9star"; "9unmodeled_at"; ":EntryDraw"; ";Model"; ";ProcInput"; ";event"; ";in_argv"; ";in_envp"; ";in_hwcap"; ";in_uid"]; [";m_halted"; ";m_vm_lazy"; "<decode_any"; "=Load"; "=SZ1"; "=SZ8"; "=instr"; ">bvmap"; "0Q"; "?msteps"; "@getr"; "@mkst"; "@rdn"; "@v_addi"; "0T"; "0brk0"]; ["0c"; "0c'"; "0c2"; "0code"; "0et"; "0evs"; "0fx"; "0imm"; "0inp"; "0isz"; "0lim"; "0limT"; "0mb"; "0mem"; "0model"; "0ms"]; ["0ms'"; "0o"; "0pc"; "0ph"; "0rd"; "0regs"; "0rnd"; "0rom"; "0rs"; "0segs"; "0sp"; "Abv"; "Abv_signed"; "0target"; "0tr"; "0w"]]).
Section WithFP1.
Context {fx : FPState}.
Lemma step_lbu_fault : ltac2:(TCodec.tc2 tcn__ErrEscape "RO'4'E%211&R7y5'S;yR0%211%5241'6y8%611%311p061yQ0%:11%;1<y<%=11'>';%<16&Q4r:r8%3221(1r5%22=1%93841'2&Q5r6%211(3%?3521'8'R6%221C%N11&R2r7%211(7(R3(R4r4%352=?D1r3%64<N21%H2<1%O3<91%QD1Q9%Q<11&R<r=&R=&R:r<%221K&S<%12Q<Q2%6231u1%:49Q921(0%11>%Q?3>31'Q6'Q7%211&Q9r>&R;vRFr;%352EB1QE%6251(Q2%11:%QL3:31p0>1p0O1p0Q@1p0QG1pUDR21pU@R41pVBR71pV:R81pW0R:1pV@R=1pULR>1pV6RE1pV<RE1pVDRL1").
Proof.
intros segs regs pc mem rom w rd rs imm isz Hfetch Hecall Hdecode Hread.
step_pipeline Hfetch Hecall Hdecode.
unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
rewrite ov_rdn, b_addsext, Hread.
reflexivity.
Qed.
Lemma step_ld_fault : ltac2:(TCodec.tc2 tcn__ErrEscape "S0'4'E%211&R7y5'S;yR0%211%5241'6y8%611%311p061yQ0%:11%;1<y<%=11'>';%<16&Q4r:r8%3221(1r5%22=1%93841'2&Q5r6%211(3%?3521'8'R6%221C%N11&R2r7%211(7(R3(R5(9r4%4532@E1r3%74=O21%I2=1%Q03=:1%QE1Q:%Q=11&R<r=&R=&R:r<%221L&S<%12Q=Q3%6231u8%:49Q:21(0%11>%Q@3>31'Q6'Q7%211&Q9r>&R;vRFr;%352EB1QF%6251(Q2%11:%QM3:31p0>1p0O1p0QA1p0QH1pUDR31pU@R51pVBR81pV:R91pW0R;1pV@R>1pULR?1pV6RF1pV<RF1pVDRM1").
Proof.
intros segs regs pc mem rom w rd rs imm isz Hfetch Hecall Hdecode Hread.
step_pipeline Hfetch Hecall Hdecode.
unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
rewrite ov_rdn, b_addsext, Hread.
reflexivity.
Qed.
Section WithSegs.
Variable segs : list Segment.
Lemma msteps_star_nil : ltac2:(TCodec.tc2 tcn__ErrEscape "Q;'Q7'QI';'6'S;yR0%211%411&R0r1%211(0%116%;3631'4'8%12::%311&R1r2%211(5%116%E3631'R9vS9r5r4%43321'QF(Q@r6%2215'QK%=11%5298%74;421p091p0?1p0J1pUNQ71pV2Q91pV0Q:1").
Proof.
intros ms ms' model Hh Hlazy H.
induction H as [ms | ms ms1 ms2 Hsvc Hstep H IH].
- apply star_refl.
- change ([] : list event) with (([] : list event) ++ []).
eapply star_step; [| exact IH].
apply (sstep_instr segs ms model ms1 model); [assumption | assumption |].
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.
Lemma msteps_illegal_error : ltac2:(TCodec.tc2 tcn__ErrEscape "QE'Q7'QI';'6'S;yR0%211%411&R0r1%211(0%116%;3631'4'8%12::%311&R1r2%211(5%116%E3631'R9vS9r5r4%43321&Q8%114%M3H1C'Q6%11Q1&Q9r6%22;1(Q2%11Q6%Q53631&QB(Q@r8%2218%42C1p061p0?1p0C1p0I1p0Q41pUNQA1pV2QC1pV0QD1").
Proof.
intros ms ms' model Hh Hlazy Hm Hsvc Hill.
exists [], (mkCfg ms' model), [].
split; [apply msteps_star_nil; assumption |].
apply sstep_instr_fault; [assumption | assumption |].
rewrite (mi_account_step_no_lazy segs ms' model Hlazy), Hill. reflexivity.
Qed.
End WithSegs.
Section OmniWithSegs.
Variable segs : list Segment.
Lemma illegal_exec : ltac2:(TCodec.tc2 tcn__ErrEscape "QO'Q7'QI';'6'S;yR0%211%411&R0r1%211(0%116%;3631'4'8%12::%311&R1r2%211(5%116%E3631&Q8r4%211%I3D1?'Q6%11M&Q9vS9r5%3221(Q2%11Q3%Q23731'K(Q@r6%2218'QK%L11'Q0':%H14%Q<34K1(Gr8r7%<221%411%QB39Q;1%9271qV4;1qVN=1%C3I@1p0E1p0O1p0Q41p0Q?1pUNQL1pV0QN1").
Proof.
intros ms model Hh Hlazy Hsvc Hill.
apply exec_step; [exact Hh | | |].
- exists [], SError. apply sstep_instr_fault; [assumption | assumption |].
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hill. reflexivity.
- intros evs Hss. inversion Hss; subst; split; reflexivity.
- intros evs c' Hnext. exfalso. inversion Hnext; subst; try congruence.
match goal with H : mi_account_step segs ms model = MachineOk _ |- _ =>
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hill in H;
discriminate
end.
Qed.
Lemma instr_exec : ltac2:(TCodec.tc2 tcn__ErrEscape "QG'Q7'QI&Q1';'6'S;yR0%211%411&R0r2%211(0%116%;3631'4'8%12::%311&R1r3%211(5%116%E3631&Q8r6%211%I3D1?'Q6%11N&Q9vS9r7%3221(Q3%12Q4:%Q23731'K(Q@%127>r5%43:21r9%521;%73=1Cp041p0:1p0D1p0I1p0Q41pTBQA1pUNQC1pV2QE1pV0QF1").
Proof.
intros ms ms' model Q Hh Hlazy Hsvc Hstep Hex.
apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
- apply (sstep_instr segs ms model ms' model); [assumption | assumption |].
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
- intros evs st Hss.
exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
- eapply exec_conseq; [exact Hex |]. intros tr o H. cbn [app]. exact H.
Qed.
Lemma msteps_exec : ltac2:(TCodec.tc2 tcn__ErrEscape "Q>'Q7'QI&Q1';'6'S;yR0%211%411&R0r2%211(0%116%;3631'4'8%12::%311&R1r3%211(5%116%E3631'R9vS9r6r5%43321'K(Q@%1254r4%43821r8%5219%73;19p041p0:1p0@1p0K1pTBQ81pUNQ:1pV2Q<1pV0Q=1").
Proof.
intros ms ms' model Q Hh Hlazy Hm Hex.
induction Hm as [ms0 | ms0 ms1 ms2 Hsvc Hstep Htail IH]; [exact Hex |].
eapply instr_exec; eauto.
Qed.
Lemma msteps_illegal_exec : ltac2:(TCodec.tc2 tcn__ErrEscape "R3'Q7'QI';'6'S;yR0%211%411&R0r1%211(0%116%;3631'4'8%12::%311&R1r2%211(5%116%E3631'R9vS9r5r4%43321&Q8%114%M3H1C'Q6%11Q1&Q9r6%22;1(Q2%11Q6%Q53631'K(Q@r8%2218'QK%O11'Q0':%K14%Q?34N1(Gr9%;21:%311%QD38Q=1%8261qV4:1qVN<1%B3Q1?1p0D1p0M1p0Q11p0Q71p0QB1pUNQO1pV2R11pV0R21").
Proof.
intros ms ms' model Hh Hlazy Hm Hsvc Hill.
eapply msteps_exec; [exact Hh | exact Hlazy | exact Hm |].
apply illegal_exec; assumption.
Qed.
Lemma fault_covered_at : ltac2:(TCodec.tc2 tcn__ErrEscape "Q='Q7'QI';'4'8'S;yR0%211%4211%611&R1r1%211(5%116%=3631'6%11:&Q8r3%211(0%11?%E3631'Q6%11I&Q9vS9r4%3221(Q2%11O%N3731&<&QG(Q@r5%2219%42;1%611p081p0B1p0K1pUNQ:1pV0Q<1").
Proof.
intros ms model Hlazy Hsvc Hfault (_ & [(_ & Hum) | (x8 & Hsvc' & _)]); cbn in *.
- rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hfault in Hum.
discriminate.
- congruence.
Qed.
Lemma msteps_illegal_errors : ltac2:(TCodec.tc2 tcn__ErrEscape "QF'Q7'QI';'6'S;yR0%211%411&R0r1%211(0%116%;3631'4'8%12::%311&R1r2%211(5%116%E3631'R9vS9r5r4%43321&Q8%114%M3H1C'Q6%11Q1&Q9r6%22;1(Q2%11Q6%Q53631'K(Q@r8%2218&J%53D21p071p0@1p0D1p0J1p0Q51pUNQB1pV2QD1pV0QE1").
Proof.
intros ms ms' model Hh Hlazy Hm Hsvc Hill.
eapply exec_conseq; [eapply msteps_illegal_exec; eassumption |].
intros tr o (_ & ->). exact I.
Qed.
Lemma msteps_illegal_covered : ltac2:(TCodec.tc2 tcn__ErrEscape "QG'Q7'QI';'6'S;yR0%211%411&R0r1%211(0%116%;3631'4'8%12::%311&R1r2%211(5%116%E3631'R9vS9r5r4%43321&Q8%114%M3H1C'Q6%11Q1&Q9r6%22;1(Q2%11Q6%Q53631'H(Q@r8%2218&I%11D%63E31p081p0A1p0E1p0K1p0Q61pUNQC1pV2QE1pV0QF1").
Proof.
intros ms ms' model Hh Hlazy Hm Hsvc Hill.
apply exec_coexec.
eapply exec_conseq; [eapply msteps_illegal_exec; eassumption |].
intros tr o (_ & ->). unfold covered. apply fault_covered_at; assumption.
Qed.
Lemma msteps_illegal_no_exit : ltac2:(TCodec.tc2 tcn__ErrEscape "QK'Q7'QI';'6'S;yR0%211%411&R0r1%211(0%116%;3631'4'8%12::%311&R1r2%211(5%116%E3631'R9vS9r5r4%43321&Q8%114%M3H1C'Q6%11Q1&Q9r6%22;1(Q2%11Q6%Q53631&<'K(Q@r9r7%3221&L%11Q6%73G31%911pU8Q<1p0<1p0E1p0I1p0O1p0Q:1pUNQG1pV2QI1pV0QJ1").
Proof.
intros ms ms' model Hh Hlazy Hm Hsvc Hill code Hex.
destruct (exec_realizes _ _ _ (msteps_illegal_exec _ _ _ Hh Hlazy Hm Hsvc Hill))
as (tr & o & Hm' & _ & ->).
exact (exec_sound _ _ _ Hex _ _ Hm').
Qed.
Lemma msteps_illegal_not_never_errors : ltac2:(TCodec.tc2 tcn__ErrEscape "QH'Q7'QI';'6'S;yR0%211%411&R0r1%211(0%116%;3631'4'8%12::%311&R1r2%211(5%116%E3631'R9vS9r5r4%43321&Q8%114%M3H1C'Q6%11Q1&Q9r6%22;1(Q2%11Q6%Q53631&<'H(Q@r8%2219&M%53E21%711p091p0B1p0F1p0L1p0Q71pUNQD1pV2QF1pV0QG1").
Proof.
intros ms ms' model Hh Hlazy Hm Hsvc Hill Hco.
destruct (exec_realizes _ _ _ (msteps_illegal_exec _ _ _ Hh Hlazy Hm Hsvc Hill))
as (tr & o & Hm' & _ & ->).
exact (coexec_sound _ _ _ _ Hm' _ Hco I).
Qed.
End OmniWithSegs.
Section AllErrorWithSegs.
Variable segs : list Segment.
Lemma illegal_all_traces_error : ltac2:(TCodec.tc2 tcn__ErrEscape "Q@'Q7'QI';'6'S;yR0%211%411&R0r1%211(0%116%;3631'4'8%12::%311&R1r2%211(5%116%E3631&Q8r4%211%I3D1?'Q6%11M&Q9vS9r5%3221(Q2%11Q3%Q23731'Q<(Q@r6%2218%42:1p061p0@1p0E1p0Q01pUNQ=1pV0Q?1").
Proof.
intros ms model Hh Hlazy Hsvc Hill.
constructor.
- exists [], SError. apply sstep_instr_fault; [assumption | assumption |].
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hill. reflexivity.
- intros evs c' Hnext. inversion Hnext; subst; try congruence.
match goal with H : mi_account_step segs ms model = MachineOk _ |- _ =>
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hill in H;
discriminate
end.
Qed.
Lemma instr_all_traces_error : ltac2:(TCodec.tc2 tcn__ErrEscape "QD'Q7'QI';'6'S;yR0%211%411&R0r1%211(0%116%;3631'4'8%12::%311&R1r2%211(5%116%E3631&Q8r5%211%I3D1?'Q6%11M&Q9vS9r6%3221(Q3%12Q3:%Q23731'Q<(Q@%127>%3291r8%421:%62<1p041p091p0C1p0H1p0Q31pUNQ@1pV2QB1pV0QC1").
Proof.
intros ms ms' model Hh Hlazy Hsvc Hstep Hall.
constructor.
- exists [], (SNext (mkCfg ms' model)).
apply (sstep_instr segs ms model ms' model); [assumption | assumption |].
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
- intros evs c' Hnext.
destruct (sstep_instr_inv segs ms model ms' evs (SNext c')
Hlazy Hsvc Hstep Hnext) as [_ Hto].
inversion Hto; subst. exact Hall.
Qed.
Lemma msteps_all_traces_error : ltac2:(TCodec.tc2 tcn__ErrEscape "Q;'Q7'QI';'6'S;yR0%211%411&R0r1%211(0%116%;3631'4'8%12::%311&R1r2%211(5%116%E3631'R9vS9r5r4%43321'Q<(Q@%1254%3271r7%4218%62:1p041p091p0?1p0J1pUNQ71pV2Q91pV0Q:1").
Proof.
intros ms ms' model Hh Hlazy Hm Hall.
induction Hm as [ms0 | ms0 ms1 ms2 Hsvc Hstep Htail IH].
- exact Hall.
- eapply instr_all_traces_error; eauto.
Qed.
Lemma msteps_illegal_all_traces_error : ltac2:(TCodec.tc2 tcn__ErrEscape "QE'Q7'QI';'6'S;yR0%211%411&R0r1%211(0%116%;3631'4'8%12::%311&R1r2%211(5%116%E3631'R9vS9r5r4%43321&Q8%114%M3H1C'Q6%11Q1&Q9r6%22;1(Q2%11Q6%Q53631'Q<(Q@r8%2218%42C1p061p0?1p0C1p0I1p0Q41pUNQA1pV2QC1pV0QD1").
Proof.
intros ms ms' model Hh Hlazy Hm Hfinal_svc Hillegal.
apply all_traces_error_iff. eapply msteps_illegal_errors; eassumption.
Qed.
End AllErrorWithSegs.
Section NoUnmodeledWithSegs.
Variable segs : list Segment.
Lemma star_stuck_refl : ltac2:(TCodec.tc2 tcn__ErrEscape "K'Q>'4'QK%211&<'QEvS9r5r2(Q;r1%211%746541%911pU6>1pU<<1'QFr4r3%34=21;';%13E3>p031p081pU4H1pVNF1pU2J1").
Proof.
intros c tr c' Hno Hstar. inversion Hstar; subst; [reflexivity|].
exfalso. eapply Hno; eassumption.
Qed.
Lemma fault_no_unmodeled : ltac2:(TCodec.tc2 tcn__ErrEscape "Q='Q7'QI';'4'8'S;yR0%211%4211%611&R1r1%211(5%116%=3631'6%11:&Q8r3%211(0%11?%E3631'Q6%11I&Q9vS9r4%3221(Q2%11O%N3731&<&QC(Q@r5%2219%42;1%611p081p0B1p0K1pUNQ:1pV0Q<1").
Proof.
intros ms model Hlazy Hsvc Hfault (tr & c & Hstar & Hun).
assert (Hno : forall evs c2, ~ sstep segs (mkCfg ms model) evs (SNext c2)).
{ intros evs c2 Hss. inversion Hss; subst; try congruence.
match goal with H : mi_account_step segs ms model = MachineOk _ |- _ =>
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hfault in H;
discriminate
end. }
rewrite (star_stuck_refl _ tr c Hno Hstar) in Hun.
destruct Hun as (_ & [(_ & Hum) | (x8 & Hsvc' & _)]); cbn in *.
- rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hfault in Hum.
discriminate.
- congruence.
Qed.
Lemma instr_no_unmodeled : ltac2:(TCodec.tc2 tcn__ErrEscape "QB'Q7'QI';'4'8'S;yR0%211%4211%611&R1r1%211(5%116%=3631'6%11:&Q8r4%211(0%11?%E3631'Q6%11I&Q9vS9r5%3221(Q3%12O<%N3731&<&QC(Q@%128A%32:1%511r7%521<%72>1%911p051p0<1p0F1p0O1pUNQ>1pV2Q@1pV0QA1").
Proof.
intros ms ms' model Hlazy Hsvc Hstep Hnext (tr & c & Hstar & Hun).
inversion Hstar as [| c1 evs c2 tr2 c3 Hss Hrest]; subst.
- destruct Hun as (_ & [(_ & Hum) | (x8 & Hsvc' & _)]); cbn in *.
+ rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep in Hum.
discriminate.
+ congruence.
- destruct (sstep_instr_inv segs ms model ms' evs (SNext c2)
Hlazy Hsvc Hstep Hss)
as [_ Hc2].
inversion Hc2; subst. apply Hnext. exists tr2, c. split; assumption.
Qed.
Lemma msteps_fault_no_unmodeled : ltac2:(TCodec.tc2 tcn__ErrEscape "QB'Q7'QI'R9vS9r3r2%43321';'4'8'S;yR0%211%4211%611&R1%11;(5%115%<3531'6%119&Q8r4%211(0%11>%D3631'Q6%11M&Q9r5%22M1(Q2%11Q2%L3631&<&QC(Q@r7%2219%42Q61%611p081p0A1p0J1p0Q81pUNQ>1pV2Q@1pV0QA1").
Proof.
intros ms ms' model Hm Hlazy Hsvc Hfault.
destruct (m_halted model) as [code |] eqn:Hh.
-
intros (tr & c & Hstar & Hun).
inversion Hstar as [| c1 evs c2 tr2 c3 Hss]; subst.
+ destruct Hun as (Hun & _). cbn in Hun. congruence.
+ pose proof (sstep_from_running segs _ _ _ Hss) as Hrun. cbn in Hrun. congruence.
- apply coexec_covered. eapply msteps_illegal_covered; eassumption.
Qed.
End NoUnmodeledWithSegs.
Lemma err_escape_omni_run : ltac2:(TCodec.tc2 tcn__ErrEscape "R8'4'E%211'='D'S;yR0%211'QH'>'QJ'Q7'R9r:&Q?r9r8r7r4&QLr2%211&QM%113&QO%115&QN%117%>9?=<;:7531r1%B3A21';'6%11J&Q8%11?(0%11N%73531'Q6%11M&Q9r<r3%3221(Q2%11Q3%@3731&O(Fr=r;%332:1r6(QA%14Q:Q8Q7Q6r5&J%:565321p0<1p0F1p0O1pV2QC1pUBQE1pUFQG1pV>QI1pUJQK1pU0QL1pVFQM1pV8R11pV6R31pVDR51").
Proof.
intros segs pc ph sp brk0 mb rnd lim inp ms' Hm Hsvc Hill.
cbn [omni_run]. unfold init_config.
eapply msteps_illegal_errors; [reflexivity | reflexivity | exact Hm | exact Hsvc | exact Hill].
Qed.
Lemma err_escape_omni_covered : ltac2:(TCodec.tc2 tcn__ErrEscape "R9'4'E%211'='D'S;yR0%211'QH'>'QJ'Q7'R9r:&Q?r9r8r7r4&QLr2%211&QM%113&QO%115&QN%117%>9?=<;:7531r1%B3A21';'6%11J&Q8%11?(0%11N%73531'Q6%11M&Q9r<r3%3221(Q2%11Q3%@3731&N(Fr=r;%332:1r6(QA%14Q:Q8Q7Q6r5&I%118%;576431p0=1p0G1p0Q01pV2QD1pUBQF1pUFQH1pV>QJ1pUJQL1pU0QM1pVFQN1pV8R21pV6R41pVDR61").
Proof.
intros segs pc ph sp brk0 mb rnd lim inp ms' Hm Hsvc Hill.
cbn [omni_corun]. unfold init_config.
eapply msteps_illegal_covered; [reflexivity | reflexivity | exact Hm | exact Hsvc | exact Hill].
Qed.
Lemma err_escape_omni_equiv : ltac2:(TCodec.tc2 tcn__ErrEscape "R>'4'E%211'='D'S;yR0%211'QH'>'QJ'C'Q:'Q7'R9r=&Q?r<r;r:r7&QLr5%211&QM%113&QO%115&QN%117%>9?=<;:7531r1%B3A21';'6%11L&Q8r2%211(0%11Q1%83631'Q6%11N&Q9r?r3%3221(Q2%11Q4%A3731&A(Fr@r>%332:1r9(QA%14Q;Q9Q8Q7r6r8%:7653Q92Q71p0<1p0F1p0Q01pV2QD1pU:QF1pUHQJ1pTNQI1pUBQK1pUFQM1pV>QO1pUJR11pU0R21pVFR31pV8R71pV6R91pVDR;1").
Proof.
intros segs pc ph sp brk0 mb rnd lim inp T limT et ms' Hm Hsvc Hill.
left. eapply err_escape_omni_run; eassumption.
Qed.
Lemma err_escape_omni_strong_equiv : ltac2:(TCodec.tc2 tcn__ErrEscape "R:'4'E%211'='D'S;yR0%211'QH'QJ'C'Q:'Q7'R9r;&Q?r:r9r8r5&QLr4%211&QM%113&QO%115&QN%117%>9?=<;:7531r1%B3A21';'6%11K&Q8r2%211(0%11Q0%83631'Q6%11N&Q9r=r3%3221(Q2%11Q4%A3731&B(Fr>r<%332:1r6(QA%14Q;Q9Q8Q7r7%95542Q81p0;1p0E1p0O1pV2QC1pU:QE1pTNQG1pUBQI1pV>QK1pUJQM1pU0QN1pVFQO1pV8R31pV6R51pVDR71").
Proof.
intros segs pc ph sp brk0 mb rnd inp T et ms' Hm Hsvc Hill.
split.
- cbn [img_segments]. eapply err_escape_omni_covered; eassumption.
- eapply err_escape_omni_equiv; eassumption.
Qed.
Lemma err_escape_equiv : ltac2:(TCodec.tc2 tcn__ErrEscape "R;'4'E%211'='D'S;yR0%211'QH'>'QJ'Q='Q7'R9r;&Q?r:r9r8r5&QLr3%211&QM%113&QO%115&QN%117%>9?=<;:7531r1%B3A21';'6%11K&Q8r2%211(0%11Q0%83631'Q6%11N&Q9r=%221H(Q2%11Q3%@3631&?&QD(Fr>r<%332:1r7(QA%14Q;Q9Q8Q7r6%945421%;21Q9p0=1p0F1p0Q01pV2QD1pVLQF1pUBQH1pUFQJ1pV>QL1pUJQN1pU0QO1pVFR01pV8R41pV6R61pVDR81").
Proof.
intros segs pc ph sp brk0 mb rnd lim inp target ms' Hm Hsvc Hill.
left. apply bh_all_errors_iff. eapply err_escape_omni_run; eassumption.
Qed.
Lemma err_escape_modeled : ltac2:(TCodec.tc2 tcn__ErrEscape "R9'4'E%211'='D'S;yR0%211'QH'>'QJ'Q7'R9r:&Q?r9r8r7r4&QLr2%211&QM%113&QO%115&QN%117%>9?=<;:7531r1%B3A21';'6%11J&Q8%11?(0%11N%73531'Q6%11M&Q9r<r3%3221(Q2%11Q3%@3731&@&QD(Fr=r;%332;1r6(QA%14Q;Q9Q8Q7r5%945421%;11p0=1p0G1p0Q01pV2QD1pUBQF1pUFQH1pV>QJ1pUJQL1pU0QM1pVFQN1pV8R21pV6R41pVDR61").
Proof.
intros segs pc ph sp brk0 mb rnd lim inp ms' Hm Hsvc Hill.
apply modeled_iff. cbn [img_segments]. eapply err_escape_omni_covered; eassumption.
Qed.
Lemma err_escape_strong_equiv : ltac2:(TCodec.tc2 tcn__ErrEscape "R?'4'E%211'='D'S;yR0%211'QH'>'QJ'Q='Q7'R9r;&Q?r:r9r8r5&QLr3%211&QM%113&QO%115&QN%117%>9?=<;:7531r1%B3A21';'6%11K&Q8r2%211(0%11Q0%83631'Q6%11N&Q9r=%221H(Q2%11Q3%@3631':&@&QD(Fr>r<%332;1r7(QA%14Q<Q:Q9Q8r6%945421%;11&?%123Q<%?231p0A1p0J1p0Q41pV2QH1pVLQJ1pUBQL1pUFQN1pV>R01pUJR21pU0R31pVFR41pV8R81pV6R:1pVDR<1").
Proof.
intros segs pc ph sp brk0 mb rnd lim inp target ms' Hm Hsvc Hill.
split; [eapply err_escape_modeled | eapply err_escape_equiv]; eassumption.
Qed.
End WithFP1.
