(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
SimInv ExitSim CatSim MmapSim ShapeAlg DivergeSim LazyFrame SymTac.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__SpinAlg () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.DivergeSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ExitSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.LazyFrame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.MmapSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg.WithSegs."; "stdpp.bitvector.definitions."], [["0A"; "0B"; "1None"; "1O"; "1Some"; "1bool"; "1cons"; "1false"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1true"]; ["1unit"; "2eq"; "2ex"; "2iff"; "2not"; "3le"; "4firstn"; "5Z"; "6len_word"; "7Segment"; "8MachineOk"; "8access_report"; "8machine_result"; "8machine_state"; "8memory_access"; "8mkAccessReport"]; ["8ms_gpr"; "8ms_read_bytes"; "8ms_svc_pending"; "8set_gpr0"; "8step"; "8step_accesses"; "9SError"; "9SNext"; "9SpuriousCfg"; "9advance_past_svc"; "9apply_effect"; "9config"; "9is_prefix"; "9mkCfg"; "9obs_trace_cfg"; "9reaches_error_cfg"]; ["9sc_alloc"; "9sstep_cfg"; "9star_cfg"; ":ENOMEM"; ":MemCopy"; ":Model"; ":errno_ret"; ":event"; ":m_fs"; ":m_halted"; ":m_vm_lazy"; ":mkEffectU"; ":page_round_up_Z"; ";buf_modeled"; ";fd1chan"; ";msteps"]; ["<spinning"; "=is_exit_no"; ">accesses_outside_lazy"; "?grant_ok"; "?mmap_args_ok"; "?mmap_model"; "?munmap_args_ok"; "?munmap_eff"; "?munmap_model"; "?page_round_up"; "@TSet"; "@node_ok"; "@realizes"; "@t_emit"; "@t_exit"; "@t_nil"]; ["@t_write_ch"; "Bsrealizes"; "Bsrz_path"; "Aspin_leaves"; "Asrealizes"; "0T"; "0T'"; "0a"; "0buf"; "0c"; "0c'"; "0e"; "0model"; "0ms"; "0ms'"; "0n"]; ["0ranges"; "0scfg"; "0segs"; "CZ_to_bv"; "Cbv"; "Cbv_and"; "Cbv_unsigned"; "0tr"; "0tr'"; "0x8"]]).
Definition spin_leaves : Prop := False.
Section WithSegs.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Inductive srealizes : config -> TSet -> Prop :=
| srz_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
(T : I -> TSet) (i0 : I),
node_ok segs scfg c I evs nx ->
(forall i, srealizes (nx i) (T i)) ->
srealizes c (t_alt (fun i => t_emit (evs i) (T i)))
| srz_halt : forall c,
m_halted (cfg_model c) <> None ->
srealizes c t_nil
| srz_spin : forall c,
to_spin segs (cfg_ms c) (cfg_model c) ->
m_halted (cfg_model c) = None ->
spin_leaves ->
srealizes c t_nil
| srz_conseq : forall c T T',
srealizes c T -> t_eq T T' -> srealizes c T'.
Lemma srealizes_of_realizes : ltac2:(TCodec.tc2 tcn__SpinAlg ">'Q;&R:'R<vS2vS1r2r1%544321'RAr3%2215p041pU<;1pUD=1").
Proof.
intros c T H;
induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq].
- exact (srz_node c I evs nx T i0 Hnode IH).
- exact (srz_halt c Hh).
- exact (srz_conseq c T T' IH Heq).
Qed.
Lemma srz_spinning : ltac2:(TCodec.tc2 tcn__SpinAlg "='Q;&R0vS2r1%3221&RC'RAr3&R?%3221p051p071pUD<1").
Proof. intros c [Hspin Hh] Hsl. exact (srz_spin c Hspin Hh Hsl). Qed.
Lemma srealizes_nonempty : ltac2:(TCodec.tc2 tcn__SpinAlg "='Q;&R:'RAr2r1%3221(;'QG%211%611p051pU<:1pUD<1").
Proof.
intros c T H;
induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh
| c Hspin Hh Hsl | c T T' H IH Heq].
- exists i0. left. apply is_prefix_nil.
- reflexivity.
- reflexivity.
- apply Heq. exact IH.
Qed.
Lemma srealizes_pclosed : ltac2:(TCodec.tc2 tcn__SpinAlg "G'Q;&R:'RAr2r1%3221'9'QG%211r4%117&Q<r3%236:1r6%113p031p071pVB:1pV@;1p0?1pU<D1pUDF1").
Proof.
intros c T H;
induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh
| c Hspin Hh Hsl | c T T' H IH Heq];
intros tr tr' HT Hp.
- destruct HT as [i [Hpre | (tr0 & -> & HT0)]]; exists i.
+ left. eapply is_prefix_trans; eauto.
+ apply is_prefix_app_split in Hp as [Hp | (tr0' & -> & Hp)].
* left. exact Hp.
* right. exists tr0'. split; [reflexivity | eapply IH; eauto].
- unfold t_nil in *. subst tr. apply is_prefix_nil_r in Hp. exact Hp.
- unfold t_nil in *. subst tr. apply is_prefix_nil_r in Hp. exact Hp.
- apply Heq. eapply IH; [apply Heq; exact HT | exact Hp].
Qed.
Lemma srealizes_star_only : ltac2:(TCodec.tc2 tcn__SpinAlg "F'Q;&R:'RAr2r1%3221'9'QG%211'QBvS2vS1r5%45321:9r3%311p031pUFA1pV@:1p0>1pU<C1pUDE1").
Proof.
intros c T H;
induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh
| c Hspin Hh Hsl | c T T' H IH Heq];
intros tr c' Hstar.
- inversion Hstar as [|c1 e c2 tr2 c3 Hss Hstar2]; subst.
+ exists i0. left. apply is_prefix_nil.
+ destruct Hnode as [_ Hsound].
destruct (Hsound e (SNext c2) Hss) as (i & -> & Heq2).
inversion Heq2; subst c2.
exists i. right. exists tr2.
split; [reflexivity | eapply IH; exact Hstar2].
- destruct (star_cfg_halted_nil segs scfg c tr c' Hh Hstar) as [-> _]. reflexivity.
- destruct c as [ms model]; cbn in Hspin, Hh.
exact (spin_star_nil segs ms model tr c' Hspin Hh (star_cfg_sub _ _ _ _ _ Hstar)).
- apply Heq. eapply IH; exact Hstar.
Qed.
Lemma srealizes_admits : ltac2:(TCodec.tc2 tcn__SpinAlg "E'Q;&R:'RAr2r1%3221'9'QG%211r3%116&Q>vS2vS1r5%44321<p061pV@91p0=1pU<B1pUDD1").
Proof.
intros c T H;
induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh
| c Hspin Hh Hsl | c T T' H IH Heq];
intros tr HT.
- destruct Hnode as [Hcomp _].
destruct HT as [i [Hpre | (tr0 & -> & HT0)]].
+ exists (evs i), (nx i). split; [apply star_cfg_one; apply Hcomp | exact Hpre].
+ destruct (IH i tr0 HT0) as (tr'' & c'' & Hstar & Hp).
exists (evs i ++ tr''), c''.
split; [eapply star_cfg_step; [apply Hcomp | exact Hstar]
| apply is_prefix_app_mono; exact Hp].
- unfold t_nil in HT; subst tr. apply obs_trace_cfg_nil.
- unfold t_nil in HT; subst tr. apply obs_trace_cfg_nil.
- apply IH. apply Heq. exact HT.
Qed.
Theorem srealizes_obs_iff : ltac2:(TCodec.tc2 tcn__SpinAlg "F'Q;&R:'RAr2r1%3221'9'QG%211&C&Q>vS2vS1r4%44321:r3%11<%8231pV@:1p0>1pU<C1pUDE1").
Proof.
intros c T H tr. split.
- intros (tr' & c' & Hstar & Hp).
eapply srealizes_pclosed;
[exact H | eapply srealizes_star_only; eauto | exact Hp].
- apply srealizes_admits; exact H.
Qed.
Lemma srealizes_step : ltac2:(TCodec.tc2 tcn__SpinAlg "L'Q;&R:'9'QG%211'RAr4r3%3221'QAvS2vS1r5(Q7r2%211%7565491'Br1%>2=1qU>C1%42D1p061p0?1pUFH1pUHE1pU<I1pUDK1").
Proof.
intros c T e c' H; revert e c';
induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh
| c Hspin Hh Hsl | c T T' H IH Heq];
intros e c' Hss.
- destruct Hnode as [_ Hsound].
destruct (Hsound e (SNext c') Hss) as (i & _ & Heq2).
inversion Heq2; subst c'. exists (T i). apply Hcont.
- exfalso. apply Hh. eapply sstep_halted_none; exact Hss.
- destruct (silent_loop_sstep segs (spinning segs) c e (SNext c')
(spinning_silent_loop segs) (conj Hspin Hh) (sstep_cfg_sub _ _ _ _ _ Hss))
as (_ & c'' & Heq2 & Hsp').
injection Heq2 as ->.
exists t_nil. exact (srz_spinning _ Hsp' Hsl).
- eapply IH; exact Hss.
Qed.
Lemma srealizes_no_sserror : ltac2:(TCodec.tc2 tcn__SpinAlg "E'Q;&R:'9'QG%211'RAr3r2%3221&D'QAvS2vS1r4(Q6%5543281%711p091pUH>1pU<B1pUDD1").
Proof.
intros c T e H; revert e;
induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh
| c Hspin Hh Hsl | c T T' H IH Heq];
intros e Hss.
- destruct Hnode as [_ Hsound].
destruct (Hsound e SError Hss) as (i & _ & Hbad). discriminate.
- apply Hh. eapply sstep_halted_none; exact Hss.
- destruct c as [ms model]; cbn in Hspin, Hh.
exact (spin_no_sstep_error segs ms model Hspin Hh e (sstep_cfg_sub _ _ _ _ _ Hss)).
- eapply IH; exact Hss.
Qed.
Definition srz_path (c : config) : Prop := exists T, srealizes c T.
Lemma srz_path_star : ltac2:(TCodec.tc2 tcn__SpinAlg "B'Q;'9'QG%211&RBr3%211'QBvS2vS1r4r2%5543271p017p081pUF?1pV@=1pUDA1").
Proof.
intros c tr c' Hp Hstar. induction Hstar as [c | c1 evs c2 tr c3 Hss Hstar IH].
- exact Hp.
- apply IH. destruct Hp as [T HT].
destruct (srealizes_step c1 T evs c2 HT Hss) as [T' HT']. exists T'. exact HT'.
Qed.
Theorem srealizes_no_error : ltac2:(TCodec.tc2 tcn__SpinAlg "@'Q;&R:'RAr2r1%3221&D&Q?vS2vS1r3%43321%611p081pU<=1pUD?1").
Proof.
intros c T H (tr & c' & evs & Hstar & Herr).
assert (Hp : srz_path c') by (eapply srz_path_star; [exists T; exact H | exact Hstar]).
destruct Hp as [T' HT']. exact (srealizes_no_sserror c' T' evs HT' Herr).
Qed.
Lemma srz_silent1 : ltac2:(TCodec.tc2 tcn__SpinAlg "G'Q;&R:&R;vS2vS1r3'@(;'QG%211q041q056%:6987621'RAr2%22:1r5%421<p031p071pU<C1pUFE1pUDF1").
Proof.
intros c c' T Hnode Hc.
apply (srz_conseq c (t_alt (fun _ : unit => t_emit [] T))).
- apply (srz_node c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode).
intros []; exact Hc.
- eapply t_eq_trans;
[ apply (t_alt_unit (fun _ : unit => t_emit [] T))
| apply t_emit_nil_eq; eapply srealizes_nonempty; exact Hc ].
Qed.
Lemma srz_emit1 : ltac2:(TCodec.tc2 tcn__SpinAlg "K'Q;'9'QG%211&R:&R;vS2vS1r4'@r3q021q034%86765421'RAr2%2281r6&R=%12;9%6231p051p091pU<C1pUHE1pUFI1pUDJ1").
Proof.
intros c c' e T Hnode Hc.
apply (srz_conseq c (t_alt (fun _ : unit => t_emit e T))).
- apply (srz_node c unit (fun _ => e) (fun _ => c') (fun _ => T) tt Hnode).
intros []; exact Hc.
- apply t_alt_unit.
Qed.
Lemma srz_alt2 : forall c (IA IB : Type) (nx : IA + IB -> config) (A B : TSet)
(a0 : IA) (b0 : IB),
node_ok segs scfg c (IA + IB) (fun _ => []) nx ->
(forall i, srealizes (nx (inl i)) A) ->
(forall i, srealizes (nx (inr i)) B) ->
srealizes c (t_alt2 A B).
Proof.
intros c IA IB nx A B a0 b0 Hnode HA HB.
assert (HA0 : A []) by (eapply srealizes_nonempty; apply (HA a0)).
assert (HB0 : B []) by (eapply srealizes_nonempty; apply (HB b0)).
apply (srz_conseq c
(t_alt (fun i : IA + IB =>
t_emit [] (match i with inl _ => A | inr _ => B end)))).
- apply (srz_node c (IA + IB) (fun _ => []) nx
(fun i => match i with inl _ => A | inr _ => B end)
(inl a0) Hnode).
intros [i|i]; [apply HA | apply HB].
- intro tr. unfold t_alt2. split.
+ intros [[i|i] Hi];
[ left; exact (proj1 (t_emit_nil_eq A HA0 tr) Hi)
| right; exact (proj1 (t_emit_nil_eq B HB0 tr) Hi) ].
+ intros [H | H];
[ exists (inl a0); exact (proj2 (t_emit_nil_eq A HA0 tr) H)
| exists (inr b0); exact (proj2 (t_emit_nil_eq B HB0 tr) H) ].
Qed.
Lemma srz_cases1 : forall c (I : Type) (nx : I -> config) (T : TSet) (i0 : I),
node_ok segs scfg c I (fun _ => []) nx ->
(forall i, srealizes (nx i) T) ->
srealizes c T.
Proof.
intros c I nx T i0 Hnode Hc.
assert (HT0 : T []) by (eapply srealizes_nonempty; apply (Hc i0)).
apply (srz_conseq c (t_alt (fun _ : I => t_emit [] T))).
- apply (srz_node c I (fun _ => []) nx (fun _ => T) i0 Hnode). exact Hc.
- intro tr. split.
+ intros [i Hi]. exact (proj1 (t_emit_nil_eq T HT0 tr) Hi).
+ intros Ht. exists i0. exact (proj2 (t_emit_nil_eq T HT0 tr) Ht).
Qed.
Lemma srz_step : ltac2:(TCodec.tc2 tcn__SpinAlg "QH'M'QE&R:'A'<'S4yR0%211%411&QIr3%211(2%116%;3631'9'>%12::%311&QJr4%211(;%116%E3631&Q2r6%211%I3D1?'L%11N&Q4vS2r7%3221(Jr5%22Q51%Q33841'RA(Q=%12?8%3216r9r8%5221%721Dp051p0:1p0E1p0J1p0Q51pU<QB1pUNQE1pUJQE1pULQG1").
Proof.
intros ms model ms' T Hh Hlazy Hsvc Hstep Hc.
eapply srz_silent1; [apply node_instr; eassumption | exact Hc].
Qed.
Lemma srz_msteps : ltac2:(TCodec.tc2 tcn__SpinAlg "Q>'M'QE&R:'A'<'S4yR0%211%411&QIr2%211(2%116%;3631'9'>%12::%311&QJr3%211(;%116%E3631'QOvS2r6r5%43321'RA(Q=%1254r4%4221r8%5219%7219p041p0:1p0@1p0K1pU<Q81pUJQ:1pUNQ<1pULQ=1").
Proof.
intros ms ms' model T Hh Hlazy Hms;
induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH];
intro Hc; [exact Hc|].
eapply srz_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep
| apply IH; exact Hc].
Qed.
Lemma node_instr_disjoint : ltac2:(TCodec.tc2 tcn__SpinAlg "QM'M'QE'9&N%211'A'<'S4yR0%211%411&QIr3%211(2%116%;3631&Q2r5%211%?3:15'L'K%11G%311&Q5vS2r6%3221(J(Or4%23Q01D%42:1%M3:61&R2&QJ%11:%3271&R;vS1(Q=r8r7%3221'@(;'QG%211q041%9278q061%=6J<8731p0?1p0D1p0Q31p0Q81pV2QE1pUNQJ1pUJQJ1pULQL1").
Proof.
intros ms model ms' ranges Hh Hsvc Hstep Hout.
pose proof (mi_account_step_disjoint segs ms model ms' ranges Hstep Hout)
as Hacc.
apply node_ok_of_pnode_instr; [exact Hsvc|].
split.
- intros []. apply (sstep_instr segs ms model ms' model); assumption.
- intros e st Hss.
inversion Hss; subst; try congruence.
match goal with
| H : mi_account_step _ _ _ = MachineOk _ |- _ =>
rewrite Hacc in H; injection H; intros; subst
end.
exists tt. split; reflexivity.
Qed.
Lemma rz_step_disjoint : ltac2:(TCodec.tc2 tcn__SpinAlg "QL'M'QE'9&N%211&R:'A'<'S4yR0%211%411&QIr4%211(2%116%;3631&Q2r6%211%?3:15'L'K%11H%311&Q5vS2r7%3221(J(Or5%23Q11D%42:1%M3:61&R2&QJ%11:%3271'R<vS1(Q=r8%22@1%54B41=r:r9%6221%94F81Np051p0<1p0A1p0Q01p0Q51pU<QB1pV2QD1pUNQI1pUJQI1pULQK1").
Proof.
intros ms model ms' ranges T Hh Hsvc Hstep Hout Hc.
eapply rz_silent1; [eapply node_instr_disjoint; eassumption | exact Hc].
Qed.
Lemma srz_step_disjoint : ltac2:(TCodec.tc2 tcn__SpinAlg "QK'M'QE'9&N%211&R:'A'<'S4yR0%211%411&QIr4%211(2%116%;3631&Q2r6%211%?3:15'L'K%11H%311&Q5vS2r7%3221(J(Or5%23Q11D%42:1%M3:61&R2&QJ%11:%3271'RA(Q=r8%22?1%421<r:r9%6221%821Mp051p0;1p0@1p0O1p0Q41pU<QA1pV2QC1pUNQH1pUJQH1pULQJ1").
Proof.
intros ms model ms' ranges T Hh Hsvc Hstep Hout Hc.
eapply srz_silent1; [eapply node_instr_disjoint; eassumption | exact Hc].
Qed.
Lemma srz_write1 : ltac2:(TCodec.tc2 tcn__SpinAlg "SC'M'QE'S4yR0%211'9y8%511%311&R:'A'<%118&QIr4%211(2%11=%83631'>%12@@%@11&QJr5%211(;%116%A3631&QNr6%211&Q2r8%211(4%12O6%J3H31'G&S6r7%22Q51+R0%Q03521&Q0r:(3%3221&S3+1%22Q>1%Q83Q>41%Q81Q;&Q1r;u1%<221u2%>241%63531%I2QCK%QB3921&QMr9%211'E&8%12QKF%32=1':r1%62@1r2r=%82R21%:231'RA(Q=&Q9&Q3rA&H&Fr3r>%33R=21%52R>1%8271%:11r@%=221%?21Bp0A1p0F1pV0I1r?%C21<&R@r<%23QA1Q=%H241p071p0Q21p0Q71p0Q;1p0QF1p0QO1p0R61p0R=1p0RA1p0RK1pU<S51pUBS71pVDS<1pUJS@1pULSB1").
Proof.
intros ms model x8 buf T Hh Hlazy Hfd Hsvc Hno Hg Hr Hbm Hnb Hc.
unfold t_write_ch.
apply (srz_node (mkCfg ms model) (wr_index buf)
(fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) buf))
(fun i => mkCfg (advance_past_svc
(set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
model)
(fun _ => T) (wr_full buf Hnb)).
- apply (node_write1 segs scfg ms model x8 buf); assumption.
- intros [n [Hn1 Hn2]]. cbn [proj1_sig]. apply Hc; assumption.
Qed.
Lemma srz_exit : ltac2:(TCodec.tc2 tcn__SpinAlg "Q?'M'QE'S4yR0%211'A'<%113&QIr2%211(2%118%83631&Q2r4%211(4%12>9%>3<31&R1r3%211'RA(Q=r6r5%3221&R>&S5&Q0(3%2271&S3+WO%22Q01%73Q141&QH%11<%;231%A2=1p0C1p0G1p0N1pVDQ81pUJQ<1pULQ>1").
Proof.
intros ms model x8 Hh Hsvc Hx8.
apply srealizes_of_realizes. apply (rz_exit segs scfg ms model x8); assumption.
Qed.
Lemma srz_munmap : ltac2:(TCodec.tc2 tcn__SpinAlg "R:'M'QE'S4yR0%211&R:'A'<%114&QIr3%211(2%119%83631'9'>%12==%311&QJr4%211(;%116%B3631&Q2r6%211(4%12I9%H3F31'G&S6r5%22O1+VG%N3521&R6r8r7%3221'RA(Q=&Q9&Q:r9&R7%112%4231%611&R8&Q0(3%2281&R9u1%52;1%311%8351D%A2:1%C21Q2r:%D21A%F21Hp041p0I1p0N1p0Q51p0Q<1p0QG1pU<R11pVDR31pUJR71pULR91").
Proof.
intros ms model x8 T Hh Hlazy Hsvc Hno Hargs Hc.
eapply srz_silent1; [apply (node_munmap segs scfg ms model x8); assumption | exact Hc].
Qed.
Lemma srz_mmap : ltac2:(TCodec.tc2 tcn__SpinAlg "SE'M'QE'S4yR0%211&R:'A'<%114&QIr3%211(2%119%83631'9'>%12==%311&QJr4%211(;%116%B3631&Q2r6%211(4%12I9%H3F31'G&S6r5%22O1+VN%N3521&R4r8%211'5&Q@vS1%211(7%Q73521&R3&Q0r;(3%3221r:r1&QLu1%8271%H2QE1%411%<48761(?%QF3D21'RA(Q=&Q9&Q:r<(QKr2y8%R311%QG11%QG2R31%QB11(6(=&R9%M2;F%211%44R:R:;1%63QN1QH'QD%QK11':%R32R?1%QN11%C6B=6QN41%F2E1%H11&R5%13F<Q9%L231r9%O221p0Q11pU@RJ1'B%QA2OQ?%R12RNE%Q=11%QE43QCQ?1%RN3QL1Q9qU@S11%72S21%Q92Q6QG%Q;21=p031p0<1p0QN1p0R51p0R91p0R@1p0RG1p0S21p4S<1pVDS>1pUJSB1pULSD1").
Proof.
intros ms model x8 B Hh Hlazy Hsvc Hno Hargs Halloc HB Hex.
destruct Hex as [a0 Ha0].
apply (srz_cases1 (mkCfg ms model) _ _ B (exist _ a0 Ha0)
(node_mmap segs scfg ms model x8 Hh Hlazy Hsvc Hno Hargs Halloc (ex_intro _ a0 Ha0))).
intros [a Ha]. cbn [proj1_sig]. apply HB. exact Ha.
Qed.
Lemma srz_mmap_nogrant : ltac2:(TCodec.tc2 tcn__SpinAlg "RC'M'QE'S4yR0%211&R:'A'<%114&QIr3%211(2%119%83631'9'>%12==%311&QJr4%211(;%116%B3631&Q2r6%211(4%12I9%H3F31'G&S6r5%22O1+VN%N3521&R4r8%211'5&R3&Q0r:(3%3221r9r1&QLu1%8271%C2Q@1%411%<48761(7%QA3?21pU@QD1'RA(Q=&Q9&Q3&QF&QC%211%42E1%611%821Dr7%;221r;%<21K%>21Q1p041p0A1p0Q31p0Q71p0Q>1p0QE1p0R01p2R:1pVDR<1pUJR@1pULRB1").
Proof.
intros ms model x8 A Hh Hlazy Hsvc Hno Hargs Hnone HA.
eapply srz_silent1; [apply (node_mmap_nogrant segs scfg ms model x8); assumption | exact HA].
Qed.
End WithSegs.
Ltac chain_mst_sp :=
first [ (eapply srz_msteps; [ sym_halted | sym_no_lazy | | ])
| chain_mst ].
Lemma chain_mst_srealizes : ltac2:(TCodec.tc2 tcn__SpinAlg "QD'9'I%211'Q8'M'QE&R:'A'<'S4yR0%211%411&QIr2%211(2%116%;3631'>%1299%E11&QJr3%211(;%116%D3631'QOr8r6r5%43321'RDr9(Q=%1265r4%544921r:%52;:%84271:p041p0;1p0A1p0K1pU<Q81pUJQ:1pUNQ<1pULQ=1pV4Q?1pV6QA1").
Proof.
intros segs scfg ms ms' model T Hh Hlazy Hms Hr.
chain_mst_sp; [exact Hms | exact Hr].
Qed.
Lemma chain_mst_srealizes_mmap : ltac2:(TCodec.tc2 tcn__SpinAlg "QI'9'I%211'Q8'M'QE'S4yR0%211&R:'A'<%114&QIr4%211(2%119%83631'>%12<<%E11&QJr5%211(;%116%A3631'QOr:r8r7%43321'RDr;(Q=&R5r6%231?7%4291%746;1Jr<%63;5<%82>1%;43:1Ep051p0>1p0D1p0N1pU<Q81pV0Q:1pU@Q;1pUJQ?1pUNQA1pULQB1pV4QD1pV6QF1").
Proof.
intros segs scfg ms ms' model a n T Hh Hlazy Hms Hr.
chain_mst_sp; [exact Hms | exact Hr].
Qed.
