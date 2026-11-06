(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SimInv ExitSim CatSim PropExec SeqExec CatExec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__WallSim () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.EquivalenceDefinition.Equivalence."; "LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.OmniRun."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.StackLayout."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall."; "LinuxProcessSemantics.Riscv.Prelude."; "LinuxProcessSemantics.Riscv.Sem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.WallSim.WithFP1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.WallSim.WithFP1.WithSegsCh."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1Some"; "1app"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1prod"; "2I"; "2and"; "2eq"; "2ex"; "2iff"; "2not"]; ["3le"; "4Forall"; "4firstn"; "4map"; "4skipn"; "5N"; "5Z"; "6equiv"; "6modeled"; "7omni_strong_equiv"; "8len_word"; "8nat_to_word"; "9PhdrInfo"; "9Segment"; "9mkImage"; ":cosafe"]; [":exec"; ":exits_with"; ":omni_run"; ":outcome"; ":post"; ";Build_machine_state"; ";MachineOk"; ";machine_result"; ";machine_state"; ";ms_read_bytes"; ";ms_svc_pending"; ";set_gpr0"; ";step"; "<SError"; "<SNext"; "<advance_past_svc"]; ["<config"; "<init_config"; "<init_machine_state"; "<is_prefix"; "<mkCfg"; "<mkEntry"; "<obs_trace"; "<reaches_error"; "<run"; "<segments_reserved"; "<sstep"; "<star"; "<step_to"; "=EntryDraw"; ">ExitEv"; ">Model"]; [">ProcInput"; ">WriteEv"; ">event"; ">in_argv"; ">in_envp"; ">in_fs"; ">in_hwcap"; ">in_uid"; ">init_model"; ">m_fs"; ">m_halted"; ">m_vm_lazy"; "?fd32"; "@bvmap"; "Areg_get"; "0Q"]; ["Bbuf_modeled"; "Bbufs_modeled"; "Bfdchan"; "Bmsteps"; "Bto_wexit"; "Bwevents"; "Bwevents_ch"; "Cfp_csr"; "Cfp_regs"; "Cgetr"; "Cmkst"; "Cregupd"; "Cv_add"; "Cv_addi"; "Cv_sub"; "Eto_wall"]; ["Eto_wall_tail"; "Eto_wallexit"; "Dto_wallexit"; "Fadd"; "Flt"; "Fof_nat"; "Fpow"; "0T"; "0abrk"; "0alim"; "0amb"; "0apc"; "0aph"; "0arnd"; "0asp"; "0b"]; ["0brk0"; "0bs"; "0bufs"; "0c"; "0ch"; "0code"; "0code'"; "0evs"; "0fd"; "0fx"; "0inp"; "0k"; "0lim"; "0mb"; "0mem"; "0model"]; ["0ms"; "0ms'"; "0n"; "0o"; "0p"; "0pc"; "0ph"; "0rbrk"; "0regs"; "0rest"; "0rlim"; "0rmb"; "0rnd"; "0rom"; "0rpc"; "0rph"]; ["0rrnd"; "0rsp"; "0segs"; "0source_segs"; "0sp"; "0st"; "GBV"; "GZ_to_bv"; "Gbv"; "Gbv_add"; "Gbv_unsigned"; "0target_segs"; "0tr"; "0tr'"; "0tr_k"]]).
Section WithFP1.
Context {fx : FPState}.
Lemma fd32_1 : ltac2:(TCodec.tc2 tcn__WallSim ":'<'THyR0%211&R<&TG+1%2251%411%93612").
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma fd32_2 : ltac2:(TCodec.tc2 tcn__WallSim ":'<'THyR0%211&R<&TG+2%2251%411%93612").
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma u_len_word : forall {A} (l : list A), (Z.of_nat (length l) < 2^64)%Z ->
bv_unsigned (len_word l) = Z.of_nat (length l).
Proof.
intros A l H. unfold len_word. apply Z_to_bv_small.
unfold bv_modulus. change (Z.of_N 64) with 64%Z. lia.
Qed.
Lemma len_word_firstn_nat : ltac2:(TCodec.tc2 tcn__WallSim "J'6'5'THy8%211%411'@r2&4r1%2261%5241'<yR0%<11&J&Br3%23>1;%42?1&K%114%:3831p0<1pW4C1pX6I1").
Proof.
intros n bs Hn. unfold len_word, nat_to_word.
rewrite firstn_length_le by exact Hn. reflexivity.
Qed.
Lemma u_len_word_firstn : ltac2:(TCodec.tc2 tcn__WallSim "Q6'6'5'THy8%211%411'@r2&4r1%2261%5241&S4&S5%62:7%211&S6+2+R0%3221%8251'<'F&TJyR0&J&Br4r3%33I21%52J1%8271%C15%<3;21p0>1p0H1pW4O1pX6Q51").
Proof.
intros n bs Hn Hlen.
rewrite len_word_unsigned by (rewrite firstn_length_le by exact Hn;
unfold two_pow_64; lia).
rewrite firstn_length_le by exact Hn. reflexivity.
Qed.
Lemma v_add_len_firstn : ltac2:(TCodec.tc2 tcn__WallSim "Q0'THyR0%211'6'5y8%611%311'@r2&4r1%2261%5241'<&RLr4&J&Br3%23>1;%42?1%7261&TI&K%116%33I:1%=3I51p0?1pW4F1pX6K1pX:M1").
Proof.
intros p n bs Hn. rewrite len_word_firstn_nat by exact Hn.
unfold v_add. apply bv_eq.
rewrite Z_to_bv_unsigned, bv_add_unsigned. reflexivity.
Qed.
Lemma v_add_len_firstn_Z : ltac2:(TCodec.tc2 tcn__WallSim "Q>'THyR0%211'6'5y8%611%311'@r2&4r1%2261%5241&S4&S5%62:7%211&S6+2+R0%3221%8251'<&RLr5&J&Br4r3%33H21%52I1%8271&TG&S3&TJ%12Q3;%F19%4221%62Q61%A3Q681p0C1p0M1pW4Q41pX6Q91pX:Q;1").
Proof.
intros p n bs Hn Hlen. unfold v_add.
rewrite u_len_word_firstn by assumption. reflexivity.
Qed.
Lemma word_add_nat_Z : ltac2:(TCodec.tc2 tcn__WallSim "O'THyR0%211'6&S4&S5r1%211&S6+2+R0%3221%8251'<&TIr3&Kr2%211%53B41&TG&S3&TJ%12F8%C17%4221%62I1%>3I81p0@1pWHJ1pX:L1").
Proof.
intros p k Hk. apply bv_eq.
rewrite bv_add_unsigned. unfold nat_to_word.
rewrite Z_to_bv_small
by (unfold bv_modulus; change (Z.of_N 64) with 64%Z; lia).
rewrite Z_to_bv_unsigned. reflexivity.
Qed.
Lemma v_sub_len_firstn : ltac2:(TCodec.tc2 tcn__WallSim "Q9'6'5'THy8%211%411'@r2&4r1%2261%5241&S4&S5%62:7%211&S6+2+R0%3221%8251'<yR0%E11&RN&Jr3%22G1&Br4%23J14%62K1%8251&D%13N58%:2O1%?3=41p0A1p0K1pW4Q21pX6Q81").
Proof.
intros n bs Hn Hlen. apply bv_eq.
rewrite v_sub_small
by (rewrite u_len_word_firstn by assumption;
rewrite len_word_unsigned by (unfold two_pow_64; lia); lia).
rewrite u_len_word_firstn by assumption.
rewrite !len_word_unsigned
by (unfold two_pow_64; rewrite ?length_skipn; lia).
rewrite length_skipn. lia.
Qed.
Section WithSegsCh.
Variable segs : list Segment.
Variable fd ch : word.
Inductive to_wall : machine_state -> list byte -> (machine_state -> Prop) -> Prop :=
| twl_write : forall ms x8 rest k,
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 64%Z ->
ms_gpr ms 0 = fd ->
ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some rest ->
(1 <= length rest)%nat ->
(forall n, (1 <= n)%nat -> (n <= length rest)%nat ->
to_wall_tail (advance_past_svc (set_gpr0 ms (len_word (firstn n rest))))
(skipn n rest) k) ->
to_wall ms rest k
with to_wall_tail : machine_state -> list byte -> (machine_state -> Prop) -> Prop :=
| twt_done : forall ms k, k ms -> to_wall_tail ms [] k
| twt_more : forall ms rest k,
(1 <= length rest)%nat ->
to_wall ms rest k ->
to_wall_tail ms rest k
| twt_step : forall ms ms' rest k,
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
to_wall_tail ms' rest k ->
to_wall_tail ms rest k.
Scheme to_wall_min := Minimality for to_wall Sort Prop
with to_wall_tail_min := Minimality for to_wall_tail Sort Prop.
Combined Scheme to_wall_mutind from to_wall_min, to_wall_tail_min.
Lemma msteps_to_wall_tail : ltac2:(TCodec.tc2 tcn__WallSim "H'Q8'5'THy8%211%411!p071'RCvTBr4r3%43321'S0r2%23541r6%43176p031p071pWH=1pXD@1pX4F1pX2G1").
Proof.
intros ms ms' rest k H; induction H; [auto|].
intro Hw. eapply twt_step; eauto.
Qed.
Lemma to_wall_tail_nil_msteps : ltac2:(TCodec.tc2 tcn__WallSim "J'Q8!p021'S0r2(7'THy8%211%411r1%83721'=';'RCvTBr4%33217r3%119%7231qX4E1%:2F1p0<1pWHF1pX2I1").
Proof.
intros ms k H.
remember ([] : list byte) as rest eqn:Hrest.
induction H as [ms k Hk | ms rest k Hnb Hw | ms ms' rest k Hsvc Hstep Ht IH].
- exists ms. split; [apply mst_refl | exact Hk].
- subst rest. cbn in Hnb. lia.
- destruct (IH Hrest) as (ms'' & Hm & Hk).
exists ms''. split; [eapply mst_step; eauto | exact Hk].
Qed.
Hypothesis Hfd32 : fd32 fd = fd.
Lemma sstep_to_wall_inv : ltac2:(TCodec.tc2 tcn__WallSim "S7'Q8'5'THy8%211%411!p071'QO'R2%911'QL'<'8yR0%=11%311&R:r3%211(0%116%:3631'9%1299%H11&R;r4%211(7%116%C3631&RBvSHvSDr5%43321&R@r8%211'ROr:r9%33215'QJvTB(QDr;%221:r7r6%746321'='6';'@u1r1%3221&4r<%22QI1%7251&C(R1%11O&B%13QO:7%54R0QK31%QI3QKK1(Q>&Q?&Q;r=&J%12R78%4231%611%Q021Q5%911%R43R5Q:1'S0&D%13R?JG%3371Q5%O251%Q02A1%Q12I1%Q22N1qX6Q41%Q62Q51p0Q81p0QA1p0QF1p0QJ1p0R01p0R:1pY<RF1pW@RH1pX0RK1pWHRM1pXDS01pX2S61").
Proof.
intros ms rest k model evs st Hh Hlazy Hfdc Hbm Hw Hss.
revert Hbm.
destruct Hw as [ms x8 rest k Hsvc Hno Hg Hr Hnb Hcont]. intro Hbm.
destruct (sstep_write_ch_inv segs fd ch Hfd32 ms model x8 rest evs st
Hh Hlazy Hfdc Hsvc Hno Hg Hr Hbm Hnb Hss) as (n & Hn1 & Hn2 & Hevs & Hst).
exists n. repeat split; try assumption.
apply (Hcont n Hn1 Hn2).
Qed.
Lemma to_wall_no_error_sstep : ltac2:(TCodec.tc2 tcn__WallSim "QO'Q8'5'THy8%211%411!p071'QO'R2%911'<'8yR0%<11%311&R:r2%211(0%116%:3631'9%1299%G11&R;r3%211(7%116%C3631&RBvSHvSDr4%43321&R@r7%211'ROr9r8%33215&?'QJvTB(QDr:%221;r6(Q=%746321%911p0;1p0@1p0D1p0J1p0Q41pW@Q@1pX0QC1pWHQE1pXDQH1pX2QN1").
Proof.
intros ms rest k model evs Hh Hlazy Hfdc Hbm Hw Hss.
destruct (sstep_to_wall_inv ms rest k model evs SError Hh Hlazy Hfdc Hbm Hw Hss)
as (n & _ & _ & _ & Hst & _).
discriminate Hst.
Qed.
Lemma to_wall_star_admits_mut : ltac2:(TCodec.tc2 tcn__WallSim "RG'QO'5'R2%211'<'8'THyR0%211%411&R:r2%211(0%116%;3631'9%1299%A11&R;r3%211(7%116%D3631&RBvSHvSDr4%43321';'Q8y8%K11%Q111!p051'ROr1%23CL1&R@%11E%>14'='Q@'QKvTB(QDr=%22M1r<%64521=qW881%:291p0<1pX4H1r7%:217&2&C(R1%11Q2r6%44NQM21r;%73QO21%E4D91LqW8G1%I2H1p0>1p0M1p0Q01pWHQ41pXDQ71pX2Q;1'S0%13QHR1Q6p017pWHQ:1pXDQ=1pX2QA1%QC271p0QE1p0QK1p0R51pYNRB1pX0RF1").
Proof.
intros model tr_k Hh Hlazy Hfdc.
apply (to_wall_mutind
(fun ms rest k =>
buf_modeled rest ->
(forall ms', k ms' -> exists c, star segs (mkCfg ms' model) tr_k c) ->
exists c, star segs (mkCfg ms model) (map (WriteEv ch) rest ++ tr_k) c)
(fun ms rest k =>
buf_modeled rest ->
(forall ms', k ms' -> exists c, star segs (mkCfg ms' model) tr_k c) ->
exists c, star segs (mkCfg ms model) (map (WriteEv ch) rest ++ tr_k) c)).
-
intros ms x8 rest k Hsvc Hno Hg Hr Hnb Hcont IH Hbm Hk.
destruct (IH (length rest) Hnb (Nat.le_refl _)
(buf_modeled_skipn (length rest) rest Hbm) Hk) as [c Hstar].
exists c.
replace (map (WriteEv ch) rest ++ tr_k)
with (map (WriteEv ch) (firstn (length rest) rest)
++ (map (WriteEv ch) (skipn (length rest) rest) ++ tr_k))
by (rewrite firstn_all, skipn_all; reflexivity).
eapply star_step; [| exact Hstar].
rewrite <- (apply_effect_copyins_no_write ms
(len_word (firstn (length rest) rest))
[(ms_gpr ms 1, length rest)]).
apply (sstep_syscall segs ms model x8
(with_copyins [(ms_gpr ms 1, length rest)]
(mkEffect (len_word (firstn (length rest) rest)) [] [])) model model
(map (WriteEv ch) (firstn (length rest) rest)));
[exact Hh | exact Hsvc | | exact Hh |].
eapply write_ch_ok_n; try eassumption. apply Nat.le_refl.
rewrite (materialize_model_accesses_no_lazy model _ Hlazy). reflexivity.
-
intros ms k Hk Hbm Hcont. cbn [map app]. apply (Hcont ms Hk).
-
intros ms rest k Hnb Hw IH Hbm Hk. exact (IH Hbm Hk).
-
intros ms ms' rest k Hsvc Hstep Ht IH Hbm Hk.
destruct (IH Hbm Hk) as [c Hstar].
exists c.
replace (map (WriteEv ch) rest ++ tr_k)
with (([] : list event) ++ (map (WriteEv ch) rest ++ tr_k)) by reflexivity.
eapply star_step; [| exact Hstar].
apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.
Lemma to_wall_star_admits : ltac2:(TCodec.tc2 tcn__WallSim "R@'Q8'5'THy8%211%411!p071'ROr3r2r1%43321&R@%115'QO'R2%@11'<'8yR0%C11%311&R:%11>(0%115%93531'9%1288%M11&R;%11G(7%115%A3531&RBvSHvSDr4%43321r9%11O'='Q@'QKvTB(QDr8%22Q81r7%64521Q8qW881%:291p0<1pX4QG1r<%:217&2&C(R1%11Gr;%44QKQ?21r6%73QA21%E4D91QGqW8G1%I2H1p0>1p0N1p0Q41p0Q=1pYNQH1pX0QK1p0QM1p0R01pWHR61pXDR91pX2R?1").
Proof.
intros ms rest k Hw Hbm model tr_k Hh Hlazy Hfdc Hk.
exact (proj1 (to_wall_star_admits_mut model tr_k Hh Hlazy Hfdc) ms rest k Hw Hbm Hk).
Qed.
Lemma to_wall_tail_star_admits : ltac2:(TCodec.tc2 tcn__WallSim "R@'Q8'5'THy8%211%411!p071'S0r3r2r1%43321&R@%115'QO'R2%@11'<'8yR0%C11%311&R:%11>(0%115%93531'9%1288%M11&R;%11G(7%115%A3531&RBvSHvSDr4%43321r9%11O'='Q@'QKvTB(QDr8%22Q81r7%64521Q8qW881%:291p0<1pX4QG1r<%:217&2&C(R1%11Gr;%44QKQ?21r6%73QA21%E4D91QGqW8G1%I2H1p0>1p0N1p0Q41p0Q=1pYNQH1pX0QK1p0QM1p0R01pWHR61pXDR91pX2R?1").
Proof.
intros ms rest k Hw Hbm model tr_k Hh Hlazy Hfdc Hk.
exact (proj2 (to_wall_star_admits_mut model tr_k Hh Hlazy Hfdc) ms rest k Hw Hbm Hk).
Qed.
Lemma to_wall_star_only_mut : ltac2:(TCodec.tc2 tcn__WallSim "RJ'QO'5'R2%211'<'8'THyR0%211%411&R:r2%211(0%116%;3631'9%1299%A11&R;r3%211(7%116%D3631&RBvSHvSDr4%43321';'Q8y8%K11%Q111!p051'ROr1%23CL1&R@%11E'Q@r6%11H'QKvTB(QDr>%22E1%5441NQ7&QC%13QBH4p031p0:1pW8=1pYJQE1pX4J1r8r=%=221%@4?1QBG&2&C(R1%11Q6%34Q1R018%53R118%A3R2Q@1p081pW8L1pYJR41p0?1p0Q01p0Q31pWHQ71pXDQ:1pX2Q>1'S0%13QKR4Q9p017pWHQ=1pXDQ@1pX2QD1%QF271p0QH1p0QN1p0R81pV@RE1pX0RI1").
Proof.
intros model T Hh Hlazy Hfdc.
apply (to_wall_mutind
(fun ms rest k =>
buf_modeled rest ->
(forall ms' tr c, k ms' -> star segs (mkCfg ms' model) tr c -> is_prefix tr T) ->
forall tr c, star segs (mkCfg ms model) tr c ->
is_prefix tr (map (WriteEv ch) rest ++ T))
(fun ms rest k =>
buf_modeled rest ->
(forall ms' tr c, k ms' -> star segs (mkCfg ms' model) tr c -> is_prefix tr T) ->
forall tr c, star segs (mkCfg ms model) tr c ->
is_prefix tr (map (WriteEv ch) rest ++ T))).
-
intros ms x8 rest k Hsvc Hno Hg Hr Hnb Hcont IH Hbm HK tr c Hstar.
inversion Hstar as [|c1 evs c2 tr2 c3 Hss Hstar2]; subst.
{ apply is_prefix_nil. }
destruct (sstep_write_ch_inv segs fd ch Hfd32 ms model x8 rest evs (SNext c2)
Hh Hlazy Hfdc Hsvc Hno Hg Hr Hbm Hnb Hss) as (n & Hn1 & Hn2 & Hevs & Hc2).
subst evs. inversion Hc2; subst c2.
pose proof (IH n Hn1 Hn2 (buf_modeled_skipn n rest Hbm) HK tr2 c Hstar2) as Hp.
rewrite <- (firstn_skipn n rest) at 2.
rewrite map_app, <- app_assoc.
apply is_prefix_app_mono. exact Hp.
-
intros ms k Hk Hbm HK tr c Hstar. cbn [map app]. exact (HK ms tr c Hk Hstar).
-
intros ms rest k Hnb Hw IH Hbm HK tr c Hstar. exact (IH Hbm HK tr c Hstar).
-
intros ms ms' rest k Hsvc Hstep Ht IH Hbm HK tr c Hstar.
inversion Hstar as [|c1 evs c2 tr2 c3 Hss Hstar2]; subst.
{ apply is_prefix_nil. }
destruct (sstep_instr_inv segs ms model ms' evs (SNext c2) Hlazy Hsvc Hstep Hss)
as [Hevs Hc2].
subst evs. inversion Hc2; subst c2. cbn [app].
exact (IH Hbm HK tr2 c Hstar2).
Qed.
Lemma to_wall_star_only : ltac2:(TCodec.tc2 tcn__WallSim "RB'Q8'5'THy8%211%411!p071'ROr3r2r1%43321&R@%115'QO'R2%@11'<'8yR0%C11%311&R:%11>(0%115%93531'9%1288%M11&R;%11G(7%115%A3531&RBvSHvSDr4%43321'Q@r;%11Q2'QKvTB(QDr9%2291%5441Q8Q7&QC%13Q3<4p031p0:1pW8=1pYJQ61pX4QH1r=r8%=221%@4?1QBQA&2&C(R1%11J%34QMQA18%53QB18%A3QCQJ1p081pW8L1pYJQE1p0?1p0Q01p0Q61p0Q?1pV@QJ1pX0QM1p0QO1p0R21pWHR81pXDR;1pX2RA1").
Proof.
intros ms rest k Hw Hbm model T Hh Hlazy Hfdc HK tr c Hstar.
exact (proj1 (to_wall_star_only_mut model T Hh Hlazy Hfdc) ms rest k Hw Hbm HK tr c Hstar).
Qed.
Lemma twl_write_rec : ltac2:(TCodec.tc2 tcn__WallSim "SA'Q8!p021'5'THy8%211%411&R=y5yR0%711%4231'8%118p041'<'F&TJ&RIr4(TF+A(:%33?21%6251%82@1+R0%<3;21&R>r5+:%;3G19%4231vSH%C3H21%G1M&Q9(Q5r6&RHvSI%211(1%I25D%22Q21(0%11Q4&RG%118r3%=8<9E642O1+;%Q03Q<1N%I2?1+<%Q33Q?1Q1%L2B1%E3741r7%A2QE1%Q=3I31'@u1&4r8%22QL1%5241'6r1%8271r2r;%92R31%<231'S0&RJ&RK&J&Br<%23R;O1%42R<1%63;QC1&RMr:+4%3221r9%=5Q@621H&D%13REQ9;r=%B3421p0D1p0I1pX6L1'RO%R?2:R:%QH2RH1%QN8<QJQ31QEQCQ9QM%431@Mp061p0Q41p0Q;1p0R61p0R>1pXLRL1pWNRM1pX<S21pXBS21pXDS81pWHS>1").
Proof.
intros k rest regs pc mem rom H17 H10 Hr Hnb Hcont.
assert (E10 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
assert (E11 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg)) by (apply bv_eq; reflexivity).
assert (E12 : Z_to_bv 5 (10 + Z.of_nat 2) = (12 : reg)) by (apply bv_eq; reflexivity).
eapply twl_write.
- cbn [ms_svc_pending]. reflexivity.
- exact H17.
- unfold ms_gpr. cbn [ms_regs]. rewrite E10. exact H10.
- unfold ms_gpr. cbn [ms_regs]. rewrite E11, E12. exact Hr.
- exact Hnb.
- intros n Hn1 Hn2. rewrite adv_set. exact (Hcont n Hn1 Hn2).
Qed.
Fixpoint to_wallexit (bufs : list (list byte)) (code : word)
(ms : machine_state) : Prop :=
match bufs with
| [] => to_wexit segs ms [] code
| buf :: rest =>
(1 <= length buf)%nat /\
to_wall_tail ms buf (to_wallexit rest code)
end.
Lemma to_wall_k_ex_mut : ltac2:(TCodec.tc2 tcn__WallSim "M';'Q8'5'THy8%211%411!p071'ROr3r2r1%43321'=%513qX4?1%32@1p051pWH;1pXD>1pX2D1'S0%13=<;p017pWHA1pXDD1pX2J1%L271").
Proof.
apply (to_wall_mutind
(fun ms rest k => exists ms', k ms')
(fun ms rest k => exists ms', k ms')).
- intros ms x8 rest k Hsvc Hno Hg Hr Hnb Hcont IH.
exact (IH (length rest) Hnb (Nat.le_refl _)).
- intros ms k Hk. exists ms. exact Hk.
- intros ms rest k Hnb Hw IH. exact IH.
- intros ms ms' rest k Hsvc Hstep Ht IH. exact IH.
Qed.
Lemma to_wall_tail_k_ex : ltac2:(TCodec.tc2 tcn__WallSim "E'Q8'5'THy8%211%411!p071'S0r3r2r1%43321'=%513qX4?1%32@1p051pWH;1pXD>1pX2D1").
Proof. exact (proj2 to_wall_k_ex_mut). Qed.
Lemma to_wallexit_bufs_nonempty : ltac2:(TCodec.tc2 tcn__WallSim "K'5'THy8%211%411%511yR0%611'Q8&S1r3r2r1%43321'A'@u1&4%12?6%4231qW0@1r4%83B21p0:1pX2@1pW<B1pW6E1").
Proof.
induction bufs as [|buf rest IH]; intros code ms Hw; [constructor|].
destruct Hw as [Hnb Hw]. constructor; [exact Hnb|].
destruct (to_wall_tail_k_ex _ _ _ Hw) as [ms' Hk].
exact (IH code ms' Hk).
Qed.
Lemma twe_step : ltac2:(TCodec.tc2 tcn__WallSim "Q7'Q8'5'THy8%211%411%511yR0%611'<'8%113&Q:r4%211(0%118%83631'Q7%11C&Q<vTBr5%3221(Q6%12I<%A3731&S1r3%23@17r7%439B1p031p071p0A1pW<K1pW6N1pX4Q51pX2Q61").
Proof.
intros ms ms' bufs code Hsvc Hstep Hw.
destruct bufs as [|buf rest].
- eapply tw_step; eauto.
- destruct Hw as [Hnb Hw]. split; [exact Hnb|].
eapply twt_step; eauto.
Qed.
Lemma msteps_to_wallexit : ltac2:(TCodec.tc2 tcn__WallSim "I'Q8'5'THy8%211%411%511yR0%611'RCvTBr4r3%43321&S1r2%23415r6%43761p031p071pW<=1pW6@1pX4G1pX2H1").
Proof.
intros ms ms' bufs code Hms Hw. destruct bufs as [|buf rest].
- exact (msteps_to_wexit segs ms ms' [] code Hms Hw).
- destruct Hw as [Hnb Hw]. split; [exact Hnb|].
eapply msteps_to_wall_tail; eauto.
Qed.
Lemma to_wall_exec_mut : ltac2:(TCodec.tc2 tcn__WallSim "RK'QO&Q4'<'8'THyR0%211%411&R:r2%211(0%116%;3631'5'9%12::%311&R;r3%211(7%116%E3631&RBvSHvSDr4%43321';'Q8y8%L11%C11!p051'ROr1%23CM1&R@%11E%>14'Q0vTB(QDr<%22Q51r;%63521p081pX4D1r6%8215'R2%Q811'Q3'=&2&C(R1%11Q2r8%44N921%63:1J%QN3:Q=1r=%12MQI%Q6231qYL>1%=2?1qX8?1qYJA1%N3MD1p0G1p0Q21p0Q51pWHQ91pXDQ<1pX2Q@1'S0%13QMR7Q;p017pWHQ?1pXDQB1pX2QF1%QH271p0QJ1p0R01p0R;1pU0RH1pX0RJ1").
Proof.
intros model Q Hh Hlazy Hfdc.
apply (to_wall_mutind
(fun ms rest k =>
buf_modeled rest ->
(forall ms', k ms' -> OmniRun.exec segs (mkCfg ms' model) Q) ->
OmniRun.exec segs (mkCfg ms model)
(fun tr o => exists tr', tr = map (WriteEv ch) rest ++ tr' /\ Q tr' o))
(fun ms rest k =>
buf_modeled rest ->
(forall ms', k ms' -> OmniRun.exec segs (mkCfg ms' model) Q) ->
OmniRun.exec segs (mkCfg ms model)
(fun tr o => exists tr', tr = map (WriteEv ch) rest ++ tr' /\ Q tr' o))).
-
intros ms x8 rest k Hsvc Hno Hg Hr Hnb Hcont IH Hbm HK.
assert (Hw : to_wall ms rest k) by (eapply twl_write; eassumption).
apply exec_step; [exact Hh | | |].
+
eexists; eexists.
apply (sstep_syscall segs ms model x8
(with_copyins [(ms_gpr ms 1, length rest)]
(mkEffect (len_word (firstn (length rest) rest)) [] [])) model model
(map (WriteEv ch) (firstn (length rest) rest)));
[exact Hh | exact Hsvc | | exact Hh |].
* eapply write_ch_ok_n; try eassumption. apply Nat.le_refl.
* rewrite (materialize_model_accesses_no_lazy model _ Hlazy). reflexivity.
+ intros evs Hss.
destruct (sstep_to_wall_inv ms rest k model evs SError Hh Hlazy Hfdc Hbm Hw Hss)
as (n & _ & _ & _ & Habs & _).
discriminate Habs.
+ intros evs c' Hss.
destruct (sstep_to_wall_inv ms rest k model evs (SNext c') Hh Hlazy Hfdc Hbm Hw Hss)
as (n & Hn1 & Hn2 & -> & Hc' & _).
injection Hc' as ->.
eapply exec_conseq;
[exact (IH n Hn1 Hn2 (buf_modeled_skipn n rest Hbm) HK) |].
intros tr o (tr' & -> & HQ). exists tr'. split; [| exact HQ].
rewrite <- (firstn_skipn n rest) at 3. rewrite map_app, <- app_assoc. reflexivity.
-
intros ms k Hk Hbm HK.
eapply exec_conseq; [exact (HK ms Hk) |].
intros tr o HQ. exists tr. split; [reflexivity | exact HQ].
-
intros ms rest k Hnb Hw IH Hbm HK. exact (IH Hbm HK).
-
intros ms ms' rest k Hsvc Hstep Ht IH Hbm HK.
apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
+ apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
+ intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
+ eapply exec_conseq; [exact (IH Hbm HK) |]. intros tr o H. cbn [app]. exact H.
Qed.
Lemma to_wexit_nil_exec_aux : ltac2:(TCodec.tc2 tcn__WallSim "R3'Q8'5'THy8%211%411%511yR0%611'QO'<'8%114&R:r1%211(0%119%83631'9%12<<%D11&R;r2%211(7%116%A3631'RDvTBr6r5r4%544321%91M%I3M51'Q0(QDr8%2218'R2%Q811'Q3';(3(QN&R9r7%211%42;1%I1:%73;21%Q:3;M1&Q1%13@OQ8%<231qX8>1qYJ@1%F3MC1p0H1p0K1p0Q21p0Q<1pX0QF1pW<QH1pW6QK1pX2R21").
Proof.
intros ms bufs code model Hh Hlazy Hte.
induction Hte as
[ms x8 Hsvc Hx8
| ms x8 buf bufs code Hsvc Hno Hg Hr Hnb Hcont IH
| ms ms' bufs code Hsvc Hstep Hte IH]; intro Hbufs; [| discriminate Hbufs |].
- apply (exec_step_only segs _ _
[ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
(mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))).
+ replace [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
with ([] ++ [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
(m_fs (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))])
by (cbn; reflexivity).
apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
(with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) []
(bv_and (ms_gpr ms 0) (Z_to_bv 64 255))).
* exact Hh.
* exact Hsvc.
* apply (exit_dispatch_ok (sys_input segs ms x8) model).
rewrite in_sysno_sys_input. exact Hx8.
* cbn. reflexivity.
* apply m_killed_with_halted.
+ intros evs st Hss. exact (sstep_exit_inv segs ms model x8 evs st Hh Hsvc Hx8 Hss).
+ apply exec_halt.
* cbn. rewrite m_halted_with_halted. discriminate.
* cbn beta. rewrite app_nil_r. split; [reflexivity |].
cbn [exits_with cfg_model]. split;
[ rewrite m_halted_with_halted; reflexivity
| apply m_killed_with_halted ].
- apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
+ apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
+ intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
+ eapply exec_conseq; [exact (IH Hbufs) |]. intros tr o H. cbn [app]. exact H.
Qed.
Lemma to_wexit_nil_exec : ltac2:(TCodec.tc2 tcn__WallSim "QN'Q8'THyR0%211'QO'<'8%114&R:r1%211(0%119%83631'5'9%12==%311&R;r2%211(7%116%B3631'RDvTBr5y8%K11%?11%911r4%847621'Q0(QDr6%2215'R2%H11'Q3';(3(QNr7&R9%11:%4231%J1:%73;21%Q<3;N1&Q1%138Q0Q:%<231qX8>1qYJ@1%F3NC1p0H1p0Q21p0Q=1pX0QG1pW<QI1pX2QM1").
Proof.
intros ms code model Hh Hlazy Hte.
exact (to_wexit_nil_exec_aux ms [] code model Hh Hlazy Hte eq_refl).
Qed.
Lemma to_wallexit_exec : ltac2:(TCodec.tc2 tcn__WallSim "R='5'THy8%211%411%511yR0%611'Q8'QO'<'8%115&R:r1%211(0%11:%83631'9%12==%E11&R;r2%211(7%116%A3631&RBvSHvSDr3%43321&RAr7%211&S1r8r6%33251'Q0vTB(QD%1295'R2%Q=11'Q3';&2&RFr;%22E1(3(QNr:&R9%11C%4231%Q11>%73?21%<3@91%QC3@Q61&Q1%139Q8QA%A231qX8C1qYJE1%K3JH1p0M1p0Q21p0Q61p0Q<1p0QF1pX0R01pX2R21pW<R41pW6R71").
Proof.
induction bufs as [|buf rest IH]; intros code ms model Hh Hlazy Hfdc Hbm Hw.
- cbn [wevents_ch app]. apply to_wexit_nil_exec; assumption.
- destruct Hw as [Hnb Hw]. apply Forall_cons_iff in Hbm as [Hb Hbs].
eapply exec_conseq;
[exact (proj2 (to_wall_exec_mut model _ Hh Hlazy Hfdc) ms buf (to_wallexit rest code)
Hw Hb (fun ms' Hk => IH code ms' model Hh Hlazy Hfdc Hbs Hk)) |].
intros tr o (tr' & -> & Heq & Hx). split; [| exact Hx].
rewrite Heq. cbn [wevents_ch]. rewrite <- app_assoc. reflexivity.
Qed.
Lemma to_wallexit_star_admits : ltac2:(TCodec.tc2 tcn__WallSim "R8'5'THy8%211%411%511yR0%611'Q8'QO'<'8%115&R:r1%211(0%11:%83631'9%12==%E11&R;r2%211(7%116%A3631&RBvSHvSDr3%43321&RAr7%211&S1r8r6%33251'='Q@'QKvTB(QD%128;&2'R2&RFr:%22D1(3(QNr9&R9%11E%4231%Q01:%73;21%=3<91%B4A?1Q>qW8D1%F2E1p0H1p0M1p0Q11p0Q71p0QA1pX0QK1pX2QM1pW<QO1pW6R21").
Proof.
intros bufs code ms model Hh Hlazy Hfdc Hbm Hw.
destruct (exec_realizes _ _ _ (to_wallexit_exec bufs code ms model Hh Hlazy Hfdc Hbm Hw))
as (tr & [c' | c'] & Hm & Heq & Hx); [| destruct Hx].
subst tr. destruct (mexec_halt_star _ _ _ _ Hm c' eq_refl) as (Hstar & _).
exists c'. exact Hstar.
Qed.
Lemma to_wallexit_no_other_exit : ltac2:(TCodec.tc2 tcn__WallSim "QO'5'THy8%211%411%511yR0%611'Q8'QO'<'8%115&R:r1%211(0%11:%83631'9%12==%E11&R;r2%211(7%116%A3631&RBvSHvSDr3%43321&RAr7%211&S1r8r6%33251&?r9%Q03Q3L1%311'Q0vTB(QD%126:&Q1%11J%63531%;11p091pW>Q>1p0?1p0D1p0H1p0N1p0Q81pX0QB1pX2QD1pW<QF1pW6QI1").
Proof.
intros bufs code ms model Hh Hlazy Hfdc Hbm Hw code' Hne Hex.
destruct (exec_realizes _ _ _ (to_wallexit_exec bufs code ms model Hh Hlazy Hfdc Hbm Hw))
as (tr & [c' | c'] & Hm & _ & Hx); [| destruct Hx].
pose proof (exec_sound _ _ _ Hex _ _ Hm) as Hx'.
cbn [exits_with] in Hx, Hx'. destruct Hx as (Hx & _). destruct Hx' as (Hx' & _).
rewrite Hx in Hx'. injection Hx' as Hx'.
exact (Hne (eq_sym Hx')).
Qed.
Lemma to_wallexit_trace_unique : ltac2:(TCodec.tc2 tcn__WallSim "R@'5'THy8%211%411%511yR0%611'Q8'QO'<'8%115&R:r1%211(0%11:%83631'9%12==%E11&R;r2%211(7%116%A3631&RBvSHvSDr3%43321&RAr7%211&S1r8r6%33251'R2%Q911&?&2&RFr:%22@1(3(QNr9&R9%11A%4231%L1=%73>21%<3?91%Q>3?Q:1%?11'Q0vTB(QD%12<H'Q3r4%QF3GQ91q031qYJI1%93861%J11p0<1pYLM1p0Q01p0Q51p0Q91p0Q?1p0QI1pX0R31pX2R51pW<R71pW6R:1").
Proof.
intros bufs code ms model Hh Hlazy Hfdc Hbm Hw tr' Hne Hex.
destruct (exec_realizes _ _ _ (to_wallexit_exec bufs code ms model Hh Hlazy Hfdc Hbm Hw))
as (tr & o & Hm & Heq & _).
pose proof (exec_sound _ _ _ Hex _ _ Hm) as Heq'. cbn beta in Heq'.
apply Hne. rewrite <- Heq', Heq. reflexivity.
Qed.
Lemma to_wallexit_not_silent : ltac2:(TCodec.tc2 tcn__WallSim "QM'5'THy8%211%411%511yR0%611'Q8'QO'<'8%115&R:r1%211(0%11:%83631'9%12==%E11&R;r2%211(7%116%A3631&RBvSHvSDr3%43321&RAr7%211&S1r8r6%33251&?'OvTB(QD%12:6'R2%Q>11%F12%Q632Q21qYJ31%93861%;11p0=1p0B1p0F1p0L1p0Q61pX0Q@1pX2QB1pW<QD1pW6QG1").
Proof.
intros bufs code ms model Hh Hlazy Hfdc Hbm Hw Hc.
destruct (to_wallexit_star_admits bufs code ms model Hh Hlazy Hfdc Hbm Hw) as (c' & Hstar).
pose proof (cosafe_star _ _ _ _ _ Hc Hstar) as Hnil.
destruct (wevents_ch ch bufs); discriminate Hnil.
Qed.
Lemma to_wallexit_star_only : ltac2:(TCodec.tc2 tcn__WallSim "R<'5'THy8%211%411%511yR0%611'Q8'QO'<'8%115&R:r1%211(0%11:%83631'9%12==%E11&R;r2%211(7%116%A3631&RBvSHvSDr3%43321&RAr7%211&S1r8r6%33251'R2%Q911'Q@'QKvTB(QDr9%221:%5441IQ2&QC&2&RFr<%22G1(3(QNr;&R9%11<%4231%Q31D%73E21%<3F91%>3GQ01p0@1pW8G1pYJI1p0L1p0Q11p0Q51p0Q;1p0QE1pX0QO1pX2R11pW<R31pW6R61").
Proof.
intros bufs code ms model Hh Hlazy Hfdc Hbm Hw tr c Hstar.
destruct (exec_realizes _ _ _
(exec_star _ _ _ _ _ (to_wallexit_exec bufs code ms model Hh Hlazy Hfdc Hbm Hw) Hstar))
as (tr' & o & _ & HQ).
cbn beta in HQ. destruct HQ as (Heq & _). rewrite <- Heq. apply is_prefix_app.
Qed.
Lemma to_wallexit_no_error : ltac2:(TCodec.tc2 tcn__WallSim "QH'Q8'QO'5'THy8%211%411%511yR0%611'<'8%113&R:r3%211(0%118%83631'9%12;;%C11&R;r4%211(7%116%A3631&RBvSHvSDr5%43321&RA%113&S1r6r8%33271&?&QGvTB(QDr9%2217%5241%711p091p0>1p0A1p0G1p0Q11pW<Q;1pW6Q>1pX0QE1pX2QG1").
Proof.
intros ms model bufs code Hh Hlazy Hfdc Hbm Hw. apply exec_no_error.
eapply exec_conseq; [exact (to_wallexit_exec bufs code ms model Hh Hlazy Hfdc Hbm Hw) |].
intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.
End WithSegsCh.
Abbreviation wexit1 segs ms bufs code :=
(to_wallexit segs (Z_to_bv 64 1) bufs code ms).
Lemma wevents_ch_fd1 : ltac2:(TCodec.tc2 tcn__WallSim "D'5'THy8%211%411%511'<'R2%811&RF&TGyR0+1%3221r1%6221&RE%113%<3:31pW6>1").
Proof.
induction bufs as [|b bs IH]; cbn [wevents_ch wevents];
[reflexivity | rewrite IH; reflexivity].
Qed.
Lemma wall_omni_run : ltac2:(TCodec.tc2 tcn__WallSim "S4'THyR0%211'<&R<r2%211%43512'5'M%211'E'L'QM'F'R0y8%A11%:11%;11&RBr>r=&R8&QIr;%211r7r6r8r4r3%96654321%=3<;1&RA%114&S2r@&QBr<r:&R3r5%211&R4%113&R7%115&R6%117%<9L;I:G7531%?5M>ED1&Q2(N%13Q1Q0?(QEr9%24Q0A1L'R2%QC11'Q3';&2&RFrB%221Q6(3(QN&R5%11Q8%32Q:1(7%11>%73?31%<3@91%R83@R61&Q1r1%23QBR91%B241qX8D1qYJF1%N5LQGIQF1p0Q01p0QA1p0QD1pW<RD1pW6R41pWFR91pWJR;1pXJR=1pWLRI1pW2RJ1pY:RK1pX>RB1pX<RD1pY6RF1p0RJ1pW:S01pWBS11").
Proof.
intros fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw.
cbn [omni_run]. unfold init_config.
exact (to_wallexit_exec segs fd ch Hfd32 bufs code _
(init_model (segments_reserved segs) brk0 mb sp lim inp)
eq_refl eq_refl Hfdc Hbm Hw).
Qed.
Lemma wall_obs_iff : ltac2:(TCodec.tc2 tcn__WallSim "S0'THyR0%211'<&R<r2%211%43512'5'M%211'E'L'QM'F'R0y8%A11%:11%;11&RBr>r=&R8&QIr;%211r7r6r8r4r3%96654321%=3<;1&RA%114&S2r@&QBr<r:&R3r5%211&R4%113&R7%115&R6%117%<9L;I:G7531%?5M>ED1'R2%Q=11&>&QFr?&QAr9%293Q6Q5DQ2C1NQ0r1%63521&QC&2&RFrA%221Q6(3(QN&R5%11Q;%32M1(7%11E%73F31%<3G91%>3H@1%G2@1pYJI1p0L1p0Q=1p0Q@1pW<R@1pW6R01pWFR51pWJR71pXJR91pWLRE1pW2RF1pY:RG1pX>R>1pX<R@1pY6RB1p0RF1pW:RL1pWBRM1").
Proof.
intros fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw tr.
apply exec_obs_iff.
eapply exec_conseq;
[exact (wall_omni_run fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw) |].
intros tr' o (Heq & Hx). split; [exact Heq | exact (exits_with_never_errors _ _ _ Hx)].
Qed.
Lemma wall_no_error_run : ltac2:(TCodec.tc2 tcn__WallSim "R<'THyR0%211'<&R<r2%211%43512'5'M%211'E'L'QM'F'R0y8%A11%:11%;11&RBr>r=&R8&QIr;%211r7r6r8r4r3%96654321%=3<;1&RA%114&S2r@&QBr<r:&R3r5%211&R4%113&R7%115&R6%117%<9L;I:G7531%?5M>ED1&?&QG&QAr9%29Q3Q2AO@1KML%42Q41%611p081p0I1p0L1pW<QL1pW6Q<1pWFQA1pWJQC1pXJQE1pWLR11pW2R21pY:R31pX>QJ1pX<QL1pY6QN1p0R21pW:R81pWBR91").
Proof.
intros fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw. apply exec_no_error.
eapply exec_conseq;
[exact (wall_omni_run fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw) |].
intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.
Lemma wall_omni_strong_equiv : ltac2:(TCodec.tc2 tcn__WallSim "RD'5'M%211'E'L'THyR0%211'QMy8%511%;11%<11'R0&S2rA&TG+1%22<1r3r2&QBr@r?r>r;&R3r1%211&R4%113&R7%115&R6%117%>9D=<;:7531%F5EBA@1r4r:r9r8r5%@1F%>1G%=1H%<1I%I9E87654321%Q15FM:L1&RA%118&I(NrDrCrB%43321r=r<%7321Q1(QE%14Q=Q6Q5Q4r7%34HGF1%=58531Jp0?1p0B1p0N1pWFQF1pW<QM1pW6QI1pVLQN1pVFR01pVBR11pVNR21pVJR61pVHR81pYHR:1pY2R51pXHR71pX@R81pY4R91pY0R=1pXNR?1pY8RA1").
Proof.
intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bufs code inp
Hsource Htarget Hbm.
assert (HfdS : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1)
(init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp))
by (split; reflexivity).
assert (HfdT : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1)
(init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp))
by (split; reflexivity).
split.
{ cbn [img_segments].
eapply coexec_conseq;
[apply exec_coexec;
exact (wall_omni_run (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1 source_segs rpc rph rsp rbrk rmb rrnd
source_alloc_limit inp bufs code HfdS Hbm Hsource) |].
intros tr o (_ & Hx).
exact (never_errors_covered _ _ _ (exits_with_never_errors _ _ _ Hx)). }
right. split.
- apply trace_equiv_iff_omni. intro tr. cbn.
rewrite (wall_obs_iff (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp bufs code HfdS Hbm Hsource tr).
rewrite (wall_obs_iff (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
target_segs apc aph asp abrk amb arnd target_alloc_limit inp bufs code HfdT Hbm Htarget tr).
reflexivity.
- apply bh_errors_iff. cbn.
apply (wall_no_error_run (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
target_segs apc aph asp abrk amb arnd target_alloc_limit inp bufs code HfdT Hbm Htarget).
Qed.
Lemma wall_strong_equiv : ltac2:(TCodec.tc2 tcn__WallSim "S1'5'M%211'E'L'THyR0%211'QM'Fy8%611%<11%=11'R0&S2rC&TG+1%22=1r3r2&QBrBrAr@r=&R3r1%211&R4%113&R7%115&R6%117%>9D=<;:7531%F5EBA@1r<r4r;r:r9r6%A1G%?1H%>1I%=1J%J9:87654321%Q25;N:M1&RAr5%211';&H&QH(NrFrErD%43321r?(QE%14Q?Q8Q7Q6%94431I%;11&Gr>%<31Q:Nr7r8%94ONM1%A4431Q1%7291%E291p0G1p0K1p0Q81pWFR01pW<R81pW6R31pVDR81pVLR:1pVFR<1pVBR=1pVNR>1pVJRB1pVHRD1pYHRF1pXFR@1pY2RB1pXHRD1pX@RE1pY4RF1pY0RJ1pXNRL1pY8RN1").
Proof.
intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
bufs code inp Hsource Htarget Hbm.
assert (HfdS : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1)
(init_model (segments_reserved source_segs) rbrk rmb rsp rlim inp))
by (split; reflexivity).
assert (HfdT : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1)
(init_model (segments_reserved target_segs) abrk amb asp alim inp))
by (split; reflexivity).
split.
{ apply no_error_run_modeled.
apply (wall_no_error_run (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
source_segs rpc rph rsp rbrk rmb rrnd rlim inp bufs code
HfdS Hbm Hsource). }
right. split.
- intro tr. cbn.
rewrite (wall_obs_iff (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
source_segs rpc rph rsp rbrk rmb rrnd rlim inp bufs code
HfdS Hbm Hsource tr).
rewrite (wall_obs_iff (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
target_segs apc aph asp abrk amb arnd alim inp bufs code
HfdT Hbm Htarget tr).
reflexivity.
- cbn.
apply (wall_no_error_run (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
target_segs apc aph asp abrk amb arnd alim inp bufs code
HfdT Hbm Htarget).
Qed.
End WithFP1.
