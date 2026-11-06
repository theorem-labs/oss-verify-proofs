(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
ShapeAlg DivergeSim SpinAlg SpinAlgX Nodes StoreOk AgentLib AgentNodes SpecConsts RefNodes LazyFrame Hoare LibWritev LibWritevX.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__DrvNodesLazyK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Init.Specif."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs."; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude."; "LinuxProcessSemantics.LinuxProcessSem.Fs."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AgentNodes."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.DrvNodesLazyK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.FileSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.LibWritev."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Nodes."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefNodes."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Scfg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0B"; "1None"; "1O"; "1Some"; "1app"; "1bool"; "1cons"; "1fst"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"]; ["1snd"; "1true"; "1unit"; "2I"; "2and"; "2eq"; "2iff"; "2not"; "2or"; "3le"; "4proj1_sig"; "5Forall"; "5firstn"; "5map"; "5skipn"; "6Z"]; ["0K"; "0KA"; "0KB"; "0L"; "7len_word"; "7word_to_nat"; "8check_syscall"; "9CheckOk"; "9CheckUnmodeled"; "9check_result"; "9check_ret_only"; "9check_ret_only_copyins"; ":file_read"; ":fs_lookup"; ":path"; ";MachineOk"]; [";access_report"; ";fetch_word"; ";is_ecall"; ";machine_result"; ";machine_state"; ";memory_access"; ";mkAccessReport"; ";ms_gpr"; ";ms_mem"; ";ms_rom"; ";ms_svc_pending"; ";set_gpr0"; ";step_accesses"; ";store_ok"; ";word_to_le_bytes"; "<SNext"]; ["<advance_past_svc"; "<apply_effect"; "<mkCfg"; "<sstep"; "<sys_input"; "=EISDIR"; "=ENAMETOOLONG"; "=ENOENT"; "=FdChannel"; "=FdDir"; "=FdEntry"; "=FdFile"; "=MemCopy"; "=Model"; "=SyscallEffect"; "=TASK_SIZE"]; ["=WriteEv"; "=alloc_fd"; "=copy_iovecs_accesses"; "=cstr_access_len_aux"; "=errno_ret"; "=event"; "=fd_insert"; "=fd_lookup"; "=fd_remove"; "=import_iovecs_accesses"; "=iov_prefix_accesses"; "=iovs_total"; "=m_fds"; "=m_fs"; "=m_halted"; "=m_vm_lazy"]; ["=materialize_model_accesses"; "=mkEffectU"; "=syscall_effect_accesses"; "=with_copyins"; "=with_fds"; ">openat_errnos"; ">openat_plain_name"; ">path_is_dirref"; "?dot_path"; "@bvmap"; "Aepend"; "Bwbytes"; "Cacc_nolazy"; "Cnolazy_rng"; "Dcheck_open_result_copyins"; "Dopen_copyins"]; ["Eiov_array"; "Eiov_bufs"; "Eiov_bufs_ok"; "Fopen_I"; "Fopen_nx"; "Ggetr"; "Gmkst"; "Grdn"; "Gregupd"; "Gseg_rom"; "Gv_addi"; "Hpath_at"; "Ifam_on"; "JTSet"; "Jnode_ok"; "Jt_alt"]; ["Jt_alt2"; "Jt_emit"; "Jt_exit"; "Jt_write_ch"; "Jwr_index"; "Ksrealizes"; "LIn"; "Lconcat"; "Madd"; "Mle"; "Mlt"; "Mmul"; "Mof_nat"; "Mpow"; "Mto_nat"; "0T"]; ["0a"; "0a0"; "0accs"; "0b1"; "0b2"; "0bn"; "0bs"; "0bs1"; "0bs2"; "0bss"; "0cnt"; "0code"; "0d"; "0data"; "0e"; "0eff"]; ["0eff0"; "0evs"; "0evs0"; "0f"; "0fd"; "0fds"; "0fuel"; "0fx"; "0i"; "0iov"; "0iovs"; "0k"; "0l1"; "0l2"; "0left"; "0m"]; ["0m'"; "0m0"; "0mem"; "0mk"; "0model"; "0mp"; "0ms"; "0n"; "0n1"; "0n2"; "0off"; "0p"; "0pc"; "0post"; "0r"; "0reads"]; ["0regs"; "0rom"; "0scfg"; "0segs"; "NBV"; "NZ_to_bv"; "Nbv"; "Nbv_add"; "Nbv_and"; "Nbv_unsigned"; "0w"; "0x8"]]).
Definition nolazy_rng (L : list (word * word)) (a : word) (n : Z) : Prop :=
forall k, (0 <= k < n)%Z -> page_in_ranges (page_base_of (bv_unsigned a + k)) L = false.
Definition acc_nolazy (L : list (word * word)) (accs : list (word * nat)) : Prop :=
forall a n, In (a, n) accs -> nolazy_rng L a (Z.of_nat n).
Lemma nolazy_rng_sub : ltac2:(TCodec.tc2 tcn__DrvNodesLazyK "H':'?'V6yR0%211%4211%611'O&S=r4r3r2%43321&T9%1234r6r5%93217p041p071p[0=1p[@>1pY2B1pR8A1").
Proof. intros L a n m H Hm k Hk. apply H. lia. Qed.
Lemma acc_nolazy_nil : ltac2:(TCodec.tc2 tcn__DrvNodesLazyK "?':'?'V6yR0%211%4211%611&S<r1(<';%:271%311%6251pR881").
Proof. intros L a n []. Qed.
Lemma acc_nolazy_cons : ltac2:(TCodec.tc2 tcn__DrvNodesLazyK "Q0':'?'V6yR0%211%4211%611';%7241%911&S=r4r3&T<r2%211%63541&S<r5%2215r6(7(>%14C@5<%33@1<%8251p071p0;1pY6C1p[@F1pY2J1pR8I1").
Proof. intros L a n accs H1 H2 a' n' [E|Hin]; [injection E as <- <-; exact H1 | exact (H2 a' n' Hin)]. Qed.
Lemma acc_nolazy_app : ltac2:(TCodec.tc2 tcn__DrvNodesLazyK "I':'?'V6yR0%211%4211%611';%7241%911&S<r3r2%3221r4%5213r5&5%13:47%9231p051p081pZL=1pZJ>1pR8B1").
Proof. intros L l1 l2 H1 H2 a n Hin. apply in_app_or in Hin as [Hin|Hin]; [exact (H1 a n Hin) | exact (H2 a n Hin)]. Qed.
Lemma acc_nolazy_one : ltac2:(TCodec.tc2 tcn__DrvNodesLazyK "Q4':'?'V6yR0%211%4211%611';'O&S=r4r3r1%43321&T9&T<%115r2%4221&S<r6(7%E2B?(>r5%24EB1?(<%115%73631%:291p0<1p0B1p[0H1p[@J1pY2N1pR8M1").
Proof. intros L a n m H Hm. apply acc_nolazy_cons; [exact (nolazy_rng_sub L a m _ H Hm) | apply acc_nolazy_nil]. Qed.
Lemma mat_id_of_nolazy : ltac2:(TCodec.tc2 tcn__DrvNodesLazyK "K'R=':'?'V6yR0%211';%5221%711&S<&ROr2%211r1%5221'E'=%11A&S0r3%2219(4%12F3%83631p0:1pY6A1p[0J1").
Proof.
intros m accs H. unfold materialize_model_accesses.
rewrite (materialize_accesses_no_new (m_vm_lazy m) (m_vm_materialized m) _ _ accs).
- rewrite with_vm_backing_id. reflexivity.
- unfold newly_materialized_pages. apply filter_all_false. intros p Hp.
destruct (accesses_pages_in accs [] p Hp) as [[] | (a & n & k & Hin & Hk & ->)].
rewrite (H a n Hin (Z.of_nat k) ltac:(lia)). reflexivity.
Qed.
Lemma with_fds_vm_lazy : ltac2:(TCodec.tc2 tcn__DrvNodesLazyK "F':'?'V6yR0%211'R:%5221%711'R='E%9266%;11&RO&S4r2r1%3221%511%613%:3821p[0<1pZ8>1").
Proof. intros f [fd vm io fsy pr lim tm]. reflexivity. Qed.
Section FPX_1. Context {fx : PropExec.FPState}.
Section WithSegs.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Lemma stepacc_ecall_epend_lz : ltac2:(TCodec.tc2 tcn__DrvNodesLazyK "R1&S9y5'V6yR0%211%5241'=y8%611%311p061yQ0%:11'E%812&QAvV3r4%3221(4r1%2291%93841'6&QBr2%211(A%?3521'QC'Q@'QD%211%411&QL&SFvU7r7r6r5%554321G%72I1(Q?(QF&S:&SE(V4+A(C%33Q@21%52=1%76?>=<Q21(<&QE%211%<3H41%>2H1%Q<3H@1p0N1p0Q51p\FQ@1p\4QC1p[6QD1p[JQK1p\2QK1").
Proof.
intros regs pc mem rom w Hfetch Hecall.
unfold RiscvSemantics.step_accesses. cbn [ms_pc ms_pc_val mkst].
rewrite Hfetch. cbv beta iota.
unfold RiscvSemantics.decode_exec_accesses. rewrite Hecall. cbv beta iota.
reflexivity.
Qed.
Lemma srz_sys_lz : ltac2:(TCodec.tc2 tcn__DrvNodesLazyK "R8&S9y5'V6yR0%211%5241'=y8%611%311p061'R=yQ0%;11&SM'E%:1<&RNr3%211(2%11A%73631%A1:&QAvV3r7%3221(4%12@;%?3731'6&QBr4%211(A%E3521'T5vV2(R2&S:vU7r:r9r8&SE(V4+A(C%33Q@21%5281%;6:987I1r6%>221%A4M@1E&SFr;%25@1?>=%C21Q0r5%G4Q3F21p071p0J1p0Q11p0Q:1pY0QC1p\FQE1p[:QH1p\4QJ1p[6QK1p[JR21p\2R21").
Proof.
intros regs pc mem rom model w T Hh HF HE Hc.
eapply (srz_step_disjoint segs scfg _ model _ [] T Hh); [reflexivity | eapply stepacc_ecall_epend_lz; eassumption | | exact Hc].
intros a n lo sz [].
Qed.
Lemma node_svc_mat : forall ms model x8 (I : Type)
(effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
(forall i, syscall_spec (sys_input segs ms x8) model (Ok (effs i) (ms' i) (evs i))) ->
(forall i, ~ spurious_refusal_cfg scfg (sys_input segs ms x8) model (effs i)) ->
(forall eff m' ev, syscall_spec (sys_input segs ms x8) model (Ok eff m' ev) ->
(exists i, eff = effs i /\ m' = ms' i /\ ev = evs i)
\/ (spurious_refusal_cfg scfg (sys_input segs ms x8) model eff /\ m_halted m' = None)) ->
~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
(forall i, m_halted (ms' i) = None) ->
(forall i, acc_nolazy (m_vm_lazy (ms' i)) (syscall_effect_accesses (effs i))) ->
node_ok segs scfg (mkCfg ms model) I evs
(fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
intros ms model x8 I effs ms' evs Hh Hsvc Hok Hns Hinv Hnu Hh' Hnl. split.
- intros i.
apply (sstep_cfg_syscall segs scfg ms model x8 (effs i) (ms' i) (ms' i) (evs i) Hh Hsvc
(Hok i) (Hns i) (Hh' i)).
apply mat_id_of_nolazy. exact (Hnl i).
- intros e st Hss.
destruct (sstep_cfg_svc_cases segs scfg ms model x8 e st Hsvc Hss)
as [(eff & model' & ev & Hspec &
[(Hnsp & Hh2 & [(m'' & -> & Hmat & ->) | (-> & Hmat & ->)]) | (code & Hh2 & -> & ->)])
| (Hum & -> & ->)].
+ destruct (Hinv _ _ _ Hspec) as [(i & -> & -> & ->) | [Hsp _]]; [| exfalso; exact (Hnsp Hsp)].
rewrite (mat_id_of_nolazy _ _ (Hnl i)) in Hmat.
injection Hmat as <-. exists i. split; reflexivity.
+ destruct (Hinv _ _ _ Hspec) as [(i & -> & -> & ->) | [Hsp _]]; [| exfalso; exact (Hnsp Hsp)].
rewrite (mat_id_of_nolazy _ _ (Hnl i)) in Hmat. discriminate.
+ destruct (Hinv _ _ _ Hspec) as [(i & -> & -> & ->) | [_ Hh3]];
[rewrite Hh' in Hh2; discriminate | rewrite Hh3 in Hh2; discriminate].
+ exfalso. exact (Hnu Hum).
Qed.
Lemma node_chk_ev_mat : forall ms model x8 (I : Type)
(effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
m_halted model = None -> ms_svc_pending ms = Some x8 ->
(forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) (evs i)) ->
(forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
(forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
(forall i, m_halted (ms' i) = None) ->
(forall i, acc_nolazy (m_vm_lazy (ms' i)) (syscall_effect_accesses (effs i))) ->
(forall i, ~ spurious_refusal_cfg scfg (sys_input segs ms x8) model (effs i)) ->
node_ok segs scfg (mkCfg ms model) I evs
(fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
intros ms model x8 I effs ms' evs Hh Hsvc Hok Hinv Hnu Hh' Hnl Hns.
apply (node_svc_mat ms model x8 I effs ms' evs Hh Hsvc).
- intros i. apply check_syscall_ok_iff. apply Hok.
- exact Hns.
- intros eff m' ev Hspec. left. apply Hinv. apply check_syscall_ok_iff. exact Hspec.
- intros Hum. apply (Hnu (mkEffect (Z_to_bv 64 0) [] [])). apply check_syscall_err_iff. exact Hum.
- exact Hh'.
- exact Hnl.
Qed.
Lemma node_det_mat : ltac2:(TCodec.tc2 tcn__DrvNodesLazyK "RN'QD'R='V6yR0%211'R>':'RE%211'E'=%117&RNr5%211(2%11<%83631&QJr7%211(4%12B9%>3<31&F'Q9&Q6&R4vV3r;r9%43321r3r:%83321(Q7r2r1%3221%N3>51'Dr8%Q13Q5:1%Q23Q:7Hr6%Q43Q581%6231%7251%H291pZ4Q91p[2QA1pZ0Q>1&G%J3ID<%L31AH(Q8%Q?3O21%511pZ0QE1%Q?1?%QC3QA1Q<&S<&RO%11Q<&S2%11H%5231&SNvV2(R2r<%221Q:'Bq01Q0&R0&R1r=%221Q<%411%:21QAq081%>6QE=:981p0@1p0G1p0J1p0Q21p0QO1p0R61pZ6R@1p[4RH1pZ2RE1p\HRG1p[:RK1p[>RM1").
Proof.
intros ms model x8 eff0 m0 evs0 Hh Hsvc Hchk Hnu Hh0 Hnl0.
assert (Hinv : forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
exists i : unit, eff = (fun _ => eff0) i /\ m' = (fun _ => m0) i /\ ev = (fun _ => evs0) i).
{ intros eff m' ev Hc. apply Hchk in Hc as (-> & -> & ->). exists tt. auto. }
apply (node_chk_ev_mat ms model x8 unit (fun _ => eff0) (fun _ => m0) (fun _ => evs0) Hh Hsvc).
- intros []. apply (proj2 (Hchk eff0 m0 evs0)). auto.
- exact Hinv.
- exact Hnu.
- intros []; exact Hh0.
- intros []; exact Hnl0.
- apply (uniform_not_spurious segs scfg ms model x8 unit (fun _ => eff0) (fun _ => m0) (fun _ => evs0)
(refusal_b (sys_input segs ms x8) model (eff_ret eff0)) Hinv).
intros []. reflexivity.
Qed.
Lemma rz_ret_only_silent_lz : ltac2:(TCodec.tc2 tcn__DrvNodesLazyK "QO'QD'R='V6yR0%211&SM'E'=%114&RNr5%211(2%119%83631&QJr7%211(4%12?9%>3<31'R>'Q9&Q6&R4vV3r9%3321;r1r8%73321&Q:r6(<'RE%211%5484J1%O3?71pZ0A1'T5vV2(R2&R0&QKr:%221M%411%621?%94G81Q6r;%9216%<4J;1Cp041p0Q71p0@1p0Q31p0Q:1pY0QD1p[2QI1p[NQG1p\HQH1p[:QL1p[>QN1").
Proof.
intros ms model x8 r m' T Hh Hsvc Hchk Hh' Hc.
eapply srz_silent1; [| exact Hc].
rewrite <- (apply_effect_no_write ms r).
apply (node_det_mat ms model x8 (mkEffect r [] []) m' [] Hh Hsvc).
- intros eff m'' evs'. rewrite Hchk. apply check_ret_only_ok_iff.
- intros eff. rewrite Hchk. apply check_ret_only_no_unmodeled.
- exact Hh'.
- apply acc_nolazy_nil.
Qed.
Lemma rz_ret_only_copyins_silent_lz : ltac2:(TCodec.tc2 tcn__DrvNodesLazyK "R='QD'R='V6yR0%211':'?';%2241%411&SM'E'=%119&RNr6%211(2%11>%83631&QJr8%211(4%12D9%>3<31'R>'Q9&Q6&R4vV3r:%3321;r1r9%73321&Q;r7r5(<'RE%211%6559K41%Q03@81pZ0B1%O17%Q33Q11L&S<&RO%11Q2%321M'T5vV2(R2&R0&QKr<%221Q4%411%621F%94N81Q=r=%9216%<4Q1;1Jp041p0?1p0D1p0G1p0Q;1p0QB1pY0QL1p[2R61p[NR41p\0R01p\HR61p[:R:1p[>R<1").
Proof.
intros ms model x8 reads r m' T Hh Hsvc Hchk Hh' Hnl Hc.
eapply srz_silent1; [| exact Hc].
rewrite <- (apply_effect_copyins_no_write ms r reads).
apply (node_det_mat ms model x8 (with_copyins reads (mkEffect r [] [])) m' [] Hh Hsvc).
- intros eff m'' evs'. rewrite Hchk. apply check_ret_only_copyins_ok_iff.
- intros eff. rewrite Hchk. apply check_ret_only_copyins_no_unmodeled.
- exact Hh'.
- unfold syscall_effect_accesses. cbn. rewrite app_nil_r. exact Hnl.
Qed.
Lemma rz_det_lz : ltac2:(TCodec.tc2 tcn__DrvNodesLazyK "S0'QD'R='V6yR0%211'R>&SM'E'=%115&RNr5%211(2%11:%83631&QJr7%211(4%12@9%>3<31':'RE%211&F'Q9&Q6&R4vV3r;r9%43321r3r:%83321(Q7r2r1%3221%Q13>51'Dr8%Q43Q6:1%Q53Q;7K(<%11G%Q83G91%7241%8261%I2:1pZ4K1p[2QC1pZ0Q@1&G%K3JE=%M31BI(Q8%QC3Q021%511pZ0QG1r6%QD11%QH3QF1QA&S<&RO%11QA&S2%11J%5231'T5vV2(R2&R0&R1r<%221Q=%411%621Q4%94QB81QNr=%9216%<4QE;1Q8p041p0?1p0F1p0J1p0Q21p0R31p0R:1pY0RD1p[4RJ1pZ2RG1p\HRI1p[:RM1p[>RO1").
Proof.
intros ms model x8 eff0 m0 T Hh Hsvc Hchk Hnu Hh0 Hnl0 Hc.
eapply srz_silent1; [eapply node_det_mat; eassumption | exact Hc].
Qed.
Lemma sstep_of_check_mat : ltac2:(TCodec.tc2 tcn__DrvNodesLazyK "R3'QD'R='V6yR0%211'R>':'RE%211'E'=%117&RNr5%211(2%11<%83631&QJr7%211(4%12B9%>3<31'Q9&Q6&R4vV3r8r6%43321%631B<(Q7r4r3%3221%K3<51&S<&RO%11:&S2%11F%5231'R3(R2r;r:%3221(QO&R0&R1%126G%311%921Q2%611%<4L8J1p0>1p0Q81p0F1p0Q41p0Q;1pZ4QE1p[2QM1pZ0QJ1p\HQL1p[:R01p[>R21").
Proof.
intros ms model x8 eff m' evs Hh Hsvc Hc Hh' Hnl.
apply (sstep_syscall segs ms model x8 eff m' m' evs Hh Hsvc).
- apply check_syscall_ok_iff. exact Hc.
- exact Hh'.
- apply mat_id_of_nolazy. exact Hnl.
Qed.
Lemma accesses_with_copyins_ret : ltac2:(TCodec.tc2 tcn__DrvNodesLazyK "O':'?'V6yR0%211';%5221%711'E&S2&S3r2(S1r1(<y8%>11%A11%A2>1%511%C2@@%711'R<%911%:1B%=6<64421%@2?1%B11%D3E1Ap[NI1p\0G1").
Proof. intros. unfold syscall_effect_accesses. cbn. apply app_nil_r. Qed.
Lemma node_open_lz : ltac2:(TCodec.tc2 tcn__DrvNodesLazyK "S3'QD'R='V6yR0%211':'?';%2241%411p069'E'=%119&RNr4%211(2%11>%83631&S<&ROr5%211r3%5221&QJr7%211(4%12J8%D3B31'R>'Q9&Q6&R4vV3r9%3321;r1r8%73321&S>r6%24154F%Q23<41pZ0>1%418%Q211%Q63Q41OpZ:Q>1%Q=2Q?Q?%Q?11%J1>%Q111r:%Q311%Q>3531pZ:QF1'R:%Q@11&RG&RL%118&RA%112%5231%QB18%QI3821&SLvV2r<%33Q421&SN(R2r=%2215&SC%117(<'RE%211q041&SD%139=Q?%<6QA?9731p0>1p0C1p0N1p0Q71p0Q<1p0QL1p0R31p0R:1p[8RD1p\0RF1p\HRL1p[:S01p[>S21").
Proof.
intros ms model x8 reads mk Hh Hnl Hsvc Hchk Hmk Hmklazy Hfree Hon.
apply node_ok_of_pnode; [| exact Hon]. split.
- intros [[e He] | []]; cbn [open_nx].
+ rewrite <- (apply_effect_copyins_no_write ms (errno_ret e) reads).
apply (sstep_of_check_mat ms model x8); [exact Hh | exact Hsvc | | exact Hh | rewrite accesses_with_copyins_ret; exact Hnl].
rewrite Hchk. apply check_open_result_copyins_ok_iff. left. exists e. auto.
+ rewrite <- (apply_effect_copyins_no_write ms (alloc_fd (m_fds model)) reads).
apply (sstep_of_check_mat ms model x8); [exact Hh | exact Hsvc | | apply Hmk | rewrite accesses_with_copyins_ret, Hmklazy; exact Hnl].
rewrite Hchk. apply check_open_result_copyins_ok_iff.
right. exists (alloc_fd (m_fds model)). auto.
- intros e st Hss.
destruct (sstep_svc_inv segs ms model x8 e st Hsvc Hss)
as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hmat & ->) | [(Hh2 & -> & Hmat & ->) | (code & Hh2 & -> & ->)]])
| (eff & Hc & -> & ->)].
+ rewrite Hchk in Hc. apply check_open_result_copyins_ok_iff in Hc.
destruct Hc as [(er & Her & -> & -> & ->) | (fd & Hlk & Heq & -> & -> & ->)].
* rewrite accesses_with_copyins_ret, (mat_id_of_nolazy _ _ Hnl) in Hmat. injection Hmat as <-.
exists (inl (exist _ er Her)). cbn [open_nx].
rewrite apply_effect_copyins_no_write. split; reflexivity.
* subst fd. rewrite accesses_with_copyins_ret, (mat_id_of_nolazy (mk _) reads) in Hmat by (rewrite Hmklazy; exact Hnl).
injection Hmat as <-.
exists (inr tt). cbn [open_nx]. rewrite apply_effect_copyins_no_write. split; reflexivity.
+ rewrite Hchk in Hc. apply check_open_result_copyins_ok_iff in Hc.
destruct Hc as [(er & Her & -> & -> & ->) | (fd & Hlk & Heq & -> & -> & ->)].
* rewrite accesses_with_copyins_ret, (mat_id_of_nolazy _ _ Hnl) in Hmat. discriminate.
* rewrite accesses_with_copyins_ret, (mat_id_of_nolazy (mk _) reads) in Hmat by (rewrite Hmklazy; exact Hnl). discriminate.
+ rewrite Hchk in Hc. apply check_open_result_copyins_ok_iff in Hc.
destruct Hc as [(er & Her & -> & -> & ->) | (fd & Hlk & Heq & -> & -> & ->)].
* congruence.
* rewrite Hmk in Hh2. discriminate.
+ exfalso. rewrite Hchk in Hc. exact (check_open_result_copyins_never_unmodeled _ _ _ _ Hc).
Qed.
Lemma rz_open_lz : ltac2:(TCodec.tc2 tcn__DrvNodesLazyK "SJ'QD'R='V6yR0%211':'?';%2241%411p069&SM'E'=%11:&RNr6%211(2%11?%83631&S<&ROr7%211r5%5221&QJr9%211(4%12K8%D3B31'R>'Q9&Q6&R4vV3r;%3321;r1r:%73321&S>r8%24154F%Q23<41pZ0>1%418%Q211%Q63Q41OpZ:Q?1%Q>2Q@Q@%Q@11%J1>%Q111r<%Q311%Q>3531pZ:QG1'R:%Q@11&RG&RL%118&RA%112%5231%QB18%QI3821&SLvV2r>%33Q421'O&T6&S5%233Q51'T5(R2&R0&QKrA&RDr2%211%5241%711r@%:221%<4QEC1Q2p0>1pYNB1r?%O11%N11%?281%A11%Q:13%D221%F4QOM1QK%F2C=&T0%12Q?R1%J4R3Q131p051p0>1p0Q21p0Q71p0QB1p0QK1p0R01p0R@1p0RG1p0RN1p4S81p2S91p[8S;1p\0S=1p\HSC1p[:SG1p[>SI1").
Proof.
intros ms model x8 reads mk A B Hh Hnl Hsvc Hchk Hmk Hmklazy Hfree Hon HA HB.
apply (srz_alt2 segs scfg (mkCfg ms model) {e : Z | In e openat_errnos} unit
(open_nx ms model mk) A B (exist _ ENOMEM ENOMEM_in_openat_errnos) tt).
- eapply node_open_lz; eassumption.
- intros [e He]. cbn [open_nx]. apply HA. exact He.
- intros []. cbn [open_nx]. exact HB.
Qed.
Lemma rz_close_lz : ltac2:(TCodec.tc2 tcn__DrvNodesLazyK "SE&S9y5'V6yR0%211%5241'=y8%611%311p061'R=yQ0%;11'R:&SM'E%;14&QAvV3r7%3221(4r4%22;1%93841'6&QBr5%211(A%?3521%J1L&RN%11>(2%11Q0%E3531&SEr;(V4+A(C%33Q:21%6251&V5+QI%22Q<1%Q03Q<41r<+:%;3QB19%>231%Q53QA1Q1&T:&V9r8%22QF1&T=+2+Q0%3221%8251%QI1QA&RG&RL%11Kr9%4221%Q?2QG=%QF3721'T5vV2(R2&SFvU7&SHr?z%Q22R<1%433M1&SJr>+4%3221r=&SI%11R4%>5=8431&S4&RH%J1Q:r:%3221%521Q=%F271%I4R=H1Q8r@%H5G1E@;%J21>%M4RAL1Q1p051p0Q01p0Q91p0QC1p0QI1p0R51p0R<1p0RC1pR2RN1pYNS01pZ:S;1p\FS31p[:S61p[6S81p[JS?1p\2S?1").
Proof.
intros regs pc mem model w fd e K HF HE Hh H17 Hfd Hfd32 Hlk Hc.
eapply srz_sys_lz; [exact Hh | exact HF | exact HE |].
eapply rz_ret_only_silent_lz; [exact Hh | reflexivity | | | rewrite adv_set_epend; exact Hc].
- intros eff. rewrite (check_syscall_57 segs) by (rewrite H17; apply u64_lit; lia).
unfold check_close. rewrite ms_gpr_epend0, Hfd, (fd32_id fd Hfd32), Hlk. reflexivity.
- rewrite with_fds_halted'. exact Hh.
Qed.
Lemma rz_ioctl_winsz_lz : forall regs (pc : word) mem model w fd e K,
fetch_word segs pc = Some w -> is_ecall w = true ->
m_halted model = None ->
getr regs 17 = Z_to_bv 64 29 ->
getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
fd_lookup (m_fds model) fd = Some e ->
match e with FdDevNull _ _ => false | FdUrandom => false | _ => true end = true ->
getr regs 11 = Z_to_bv 64 0x5413 ->
srealizes segs scfg (mkCfg (mkst (regupd regs 10 (errno_ret ENOTTY)) (v_addi pc 4) mem (seg_rom segs))
model) K ->
srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
intros regs pc mem model w fd e K HF HE Hh H17 Hfd Hfd32 Hlk Hnd H11 Hc.
eapply srz_sys_lz; [exact Hh | exact HF | exact HE |].
eapply rz_ret_only_silent_lz; [exact Hh | reflexivity | | exact Hh | rewrite adv_set_epend; exact Hc].
intros eff. rewrite check_syscall_29 by (rewrite H17; apply u64_lit; lia).
unfold check_ioctl. rewrite ms_gpr_epend0, ms_gpr_epend1, Hfd, (fd32_id fd Hfd32), Hlk, H11.
destruct e; first [reflexivity | discriminate Hnd].
Qed.
Lemma rz_read_dir_lz : ltac2:(TCodec.tc2 tcn__DrvNodesLazyK "T0&S9y5'V6yR0%211%5241'=y8%611%311p061'R=yQ0%;11&SM'E%:13&QAvV3r6%3221(4r3%22:1%93841'6&QBr4%211(A%?3521%I1K&RN%11>(2%11O%E3531&SEr:(V4+A(C%33Q921%6251&V5+QO%22Q;1%Q03Q;41r;+:%;3QA19%>231%Q53Q@1Q1&T:&V9r7%22QE1&T=+2+Q0%3221%8251'R:%QI11&RG&RL%11Lr8%4221(R9%QA281%QH3831&T9&T8r>+;%Q53R;1Q3%Q8231%H2R;1+<%Q93R?1Q7%Q<271%L2R?1%:251&R?%=221'T5vV2(R2&SFvU7&SHr?&RD&R5%211%534Q>1&SJ+4%22I1r=&SI%11RD%>5=7431r<%A221r9%E4RID21r@%D5C1AQ37%F21:%I4RMH1R9p051p0L1p0Q;1p0QF1p0R01p0R61p0RB1p0RI1p0S01pR2S;1pZ:SF1p\FS>1p[:SA1p[6SC1p[JSJ1p\2SJ1").
Proof.
intros regs pc mem model w fd K HF HE Hh H17 Hfd Hfd32 Hlk Hts Hc.
eapply srz_sys_lz; [exact Hh | exact HF | exact HE |].
eapply rz_ret_only_silent_lz; [exact Hh | reflexivity | | exact Hh | rewrite adv_set_epend; exact Hc].
intros eff. rewrite (check_syscall_63 segs _ _ eff model) by (rewrite H17; apply u64_lit; lia).
unfold check_read. rewrite ms_gpr_epend0, ms_gpr_epend1, ms_gpr_epend2, Hfd, (fd32_id fd Hfd32), Hlk.
rewrite (access_okb_intro_le _ _ (proj1 (bv_unsigned_in_range 64 (getr regs 12))) Hts).
reflexivity.
Qed.
Lemma rz_read_dir_cnt_lz : ltac2:(TCodec.tc2 tcn__DrvNodesLazyK "T7&S9y5'V6yR0%211%5241'=y8%611%311p061'R=yQ0%;11'O&SM'E%;14&QAvV3r7%3221(4r4%22;1%93841'6&QBr5%211(A%?3521%J1L&RN%11>(2%11Q0%E3531&SEr;(V4+A(C%33Q:21%6251&V5+QO%22Q<1%Q03Q<41r<+:%;3QB19%>231%Q53QA1Q1&T:&V9r8%22QF1&T=+2+Q0%3221%8251'R:%QJ11&RG&RL%11Lr9%4221(R9%QA281%QH3831r?+<%Q33R:1Q1%Q6231%Q02R:9%QN3R:21&T9zr:%3221&T8rA+;%Q>3RE1Q<%QA231%Q12RE1%621QB&R?%<221'T5vV2(R2&SFvU7&SHrB&RD&R5%211%534QC1&SJ+4%22E1r@&SI%11RI%>5=7431%@21Q5%C4RLB1R8rC%B5A1?M5%D218%G4S0F1R2p051p0J1p0Q41p0Q91p0Q@1p0QK1p0R51p0R;1p0RG1p0RN1p0S51pR2S@1pYFSB1pZ:SM1p\FSE1p[:SH1p[6SJ1p[JT11p\2T11").
Proof.
intros regs pc mem model w fd cnt K HF HE Hh H17 Hfd Hfd32 Hlk H12 Hc0 Hts Hc.
eapply (rz_read_dir_lz regs pc mem model w fd K); try eassumption.
rewrite H12, u64_lit; [exact Hts|]. unfold TASK_SIZE in Hts. pose proof (u64_range (getr regs 11)). lia.
Qed.
Lemma rz_read_file_lz : ltac2:(TCodec.tc2 tcn__DrvNodesLazyK "V1&S9y5'V6yR0%211%5241'=y8%611%311p061'R=yQ0%;11&Q>':%118'O&SM'E%>17&QAvV3r:%3221(4r7%22>1%93841'6&QBr8%211(A%?3521%M1O&RN%11>(2%11Q3%E3531&SEr>(V4+A(C%33Q=21%6251&V5+QO%22Q?1%Q03Q?41r?+:%;3QE19%>231%Q53QD1Q1&T:&V9r;%22QI1&T=+2+Q0%3221%8251'R:%QM11&RG&RL%11Lr<%4221(R;%12?QC%QB291%QI3941%R71QM&Q=&RM%11L%321:%QI2R2QK%R03621rC+<%Q;3RE1Q9%Q>231%Q82RER1%R63RE21&T9+1%221Q1+RPP0%42G1r=+R0%Q42Q31%Q9231&QMrErG+;%QL3S61QJ%QO231&T>%11R0%84RE731%RI3R?1R;&T8rH%R6218%QF2S=1%421QM&R?%I221&S=&ROrF%211rI%R@21Br@%73421&Q<rBrJ%RF21Q9%433Q<1'T5vV2(R2&SFvU7&SHrK&Q4r1%22T21%534RE1&SJ+4%22@1&S;%S729Q9%23I18&SI%11SM%@5?9631&S4&RF%RB1Q9&V7rD%23TG1@%RB2QG1%635Q61%821Q?%K2:1rA%O4T:N21rL%N5M1KQ4?%Q021Q;%Q34T>Q21Q7p051tY>TFQ61p0Q<1p0QE1p0QM1p0R81p0R=1p0R@1p0RD1p0RK1p0S31p0S?1p0SI1p0SO1p0T;1p0TB1p0TI1pR2U41pYFU61pYLU81p[FUE1p[HU<1pZ:UG1p\FU?1p[:UB1p[6UD1p[JUK1p\2UK1").
Proof.
intros regs pc mem model w fd p off data cnt K HF HE Hh H17 Hfd Hfd32 Hlk Hfs H12 Hc1 Hmax H64 Hok Hts Hnl bs Hc.
assert (Hno : bv_unsigned (getr regs 17) = 63%Z) by (rewrite H17; apply u64_lit; lia).
eapply srz_sys_lz; [exact Hh | exact HF | exact HE |].
destruct (read_bytes_map_of_store_ok segs mem (getr regs 11) (Z.to_nat cnt) Hok ltac:(lia)) as [wv Hw].
rewrite Z2Nat.id in Hw by lia.
set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
assert (Hu2 : bv_unsigned (ms_gpr ms 2) = cnt).
{ unfold ms. rewrite ms_gpr_epend2, H12. apply u64_lit. lia. }
destruct (read_file_check segs ms (getr regs 17) model fd p off data wv Hno
ltac:(unfold ms; rewrite ms_gpr_epend0; exact Hfd) Hfd32 Hlk Hfs
ltac:(unfold ms; rewrite ms_writable_byte_epend, ms_gpr_epend1, ms_gpr_epend2, H12; exact Hw)
ltac:(rewrite Hu2; lia) ltac:(rewrite Hu2; exact Hmax)
ltac:(rewrite Hu2; unfold ms; rewrite ms_gpr_epend1; apply access_okb_intro_le; lia)) as [Hchk Hnu].
unfold ms in Hchk, Hnu. rewrite ms_gpr_epend1, ms_gpr_epend2 in Hchk.
assert (Hlen : (Z.of_nat (length bs) <= cnt)%Z).
{ subst bs. rewrite length_file_read. unfold word_to_nat. rewrite H12, u64_lit by lia. lia. }
subst bs. revert Hc Hchk Hlen.
generalize (file_read data off (getr regs 12)) as bs. intros bs Hc Hchk Hlen.
eapply (rz_det_lz _ model _ (mkEffect (len_word bs) (delivered_writes (getr regs 11) bs) [])
(with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model));
[exact Hh | reflexivity | exact Hchk | exact Hnu
| rewrite with_fds_halted'; exact Hh | | ].
- rewrite with_fds_vm_lazy. unfold syscall_effect_accesses. cbn [eff_copyins eff_writes app].
destruct bs as [|b bsr]; cbn [delivered_writes write_accesses length]; [apply acc_nolazy_nil|].
apply (acc_nolazy_one _ _ _ cnt Hnl Hlen).
- destruct bs as [|b bsr]; cbn [delivered_writes].
+ unfold ms. rewrite adv_ret_epend. cbn [wbytes] in Hc. exact Hc.
+ unfold ms. rewrite adv_write1_epend. exact Hc.
Qed.
Lemma cstr_access_len_aux_le : ltac2:(TCodec.tc2 tcn__DrvNodesLazyK "C'V6yR0%211'=y8%511%311p051';'I&RCr3r1r2%43321%6212pY2>1pZ>91p[<;1").
Proof.
intros mp fuel. induction fuel as [|f IH]; intros a; cbn [cstr_access_len_aux]; [lia|].
destruct (mp a) as [b|]; [|lia]. destruct (bv_eqb b (Z_to_bv 8 0)); [lia|]. specialize (IH (a + 1)). lia.
Qed.
Section OpenatLz.
Variables (regs : bvmap 5 word) (pc : word) (mem : word -> option byte) (model : Model).
Variable w : bv 32.
Hypothesis HF : fetch_word segs pc = Some w.
Hypothesis HE : is_ecall w = true.
Hypothesis Hh : m_halted model = None.
Hypothesis H17 : getr regs 17 = Z_to_bv 64 56.
Hypothesis H10 : getr regs 10 = AT_FDCWD.
Hypothesis Hfl : Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z.
Hypothesis Hfs_on : sc_fs scfg = true.
Hypothesis Hnl : nolazy_rng (m_vm_lazy model) (getr regs 11) 4096.
Let ms := epend regs pc mem (seg_rom segs) (getr regs 17).
Let post (r : word) := mkst (regupd regs 10 r) (v_addi pc 4) mem (seg_rom segs).
Let fds := m_fds model.
Lemma open_copyins_nolazy : ltac2:(TCodec.tc2 tcn__DrvNodesLazyK "8&S<&ROvUD%211&S?vUF%211%7241").
Proof.
unfold open_copyins. cbv delta [ms]. rewrite ms_gpr_epend1.
eapply acc_nolazy_one; [exact Hnl|].
pose proof (cstr_access_len_aux_le (ms_read_byte (epend regs pc mem (seg_rom segs) (getr regs 17))) path_max (getr regs 11)) as Hle.
unfold path_max in Hle at 2. lia.
Qed.
Lemma rz_openat_toolong_lz : ltac2:(TCodec.tc2 tcn__DrvNodesLazyK "QK':'V6y8%211%411&SM'E'=%114&SGvV3vUB&SEvV0(V4y5+;(C%43321%7261uTP0%<4;:21(4r2%22D1%C3A41&G&T6&V5z%22L1r3%53M21%711'T5vV2(R2vUM&RD&R6%211%411vUD%7221%:4Q291=&SFvU7vUL&SI%11Q7%554Q53Q71%?219r4%C4Q;B21p0:1p0F1p0O1pR2QD1pY>QF1").
Proof.
intros bs K Hrd Hnz Hc. cbv delta [post] in *.
pose proof (read_cstr_toolong_of_rdn segs mem (getr regs 11) bs (rdn_length _ _ _ _ _ Hrd) Hnz Hrd) as Hp.
eapply srz_sys_lz; [exact Hh | exact HF | exact HE |].
eapply rz_ret_only_copyins_silent_lz; [exact Hh | reflexivity | | exact Hh | exact open_copyins_nolazy | rewrite adv_set_epend; exact Hc].
intros eff. fold ms. rewrite (openat_check_head segs regs pc mem model H17 H10 Hfl), Hp. apply check_copyins_after_ret_only.
Qed.
Lemma rz_openat_empty_lz : ltac2:(TCodec.tc2 tcn__DrvNodesLazyK "Q3&SM&SKvV3vV0vUB(<'V6y8%211%411%948761'T5vV2(R2vUM&RD&R7%211%411vUD%7221r2%;4D:21&SFvU7vUL&SI%11I%554I3H1%@21:r3%D4MC21p0:1p0G1pR2Q21").
Proof.
intros K Hp Hc. cbv delta [post] in *.
eapply srz_sys_lz; [exact Hh | exact HF | exact HE |].
eapply rz_ret_only_copyins_silent_lz; [exact Hh | reflexivity | | exact Hh | exact open_copyins_nolazy | rewrite adv_set_epend; exact Hc].
intros eff. fold ms. rewrite (openat_check_head segs regs pc mem model H17 H10 Hfl), (path_at_cstr segs regs mem [] Hp). apply check_copyins_after_ret_only.
Qed.
Lemma rz_openat_absent_lz : ltac2:(TCodec.tc2 tcn__DrvNodesLazyK "QN':'V6y8%211%411&SM&SKvV3vV0vUBr2%544321&G'Er3(<%11=%43=31%611'6&S6r4%211(A%;3521'=%11F&Q=&RMvUD%211r5%5221(2%11N%F3931'T5vV2(R2vUM&RD&R7%211%411%621?%94Q681>&SFvU7vUL&SI%11Q;%554Q;3Q:1%>21Gr6%B4Q?A21p0:1p0E1p0Q11p0Q81p0Q@1pR2QG1p[HQI1").
Proof.
intros p K Hp Hne Hpl Hfs Hc. cbv delta [post] in *.
eapply srz_sys_lz; [exact Hh | exact HF | exact HE |].
eapply rz_ret_only_copyins_silent_lz; [exact Hh | reflexivity | | exact Hh | exact open_copyins_nolazy | rewrite adv_set_epend; exact Hc].
intros eff. fold ms. rewrite (openat_check_head segs regs pc mem model H17 H10 Hfl), (path_at_cstr segs regs mem p Hp).
rewrite (path_eqb_neq _ _ Hne), (openat_plain_name_noslash _ Hpl), (openat_plain_name_nodirref _ Hpl), Hfs.
apply check_copyins_after_ret_only.
Qed.
Hypothesis Hfree : fd_lookup fds (alloc_fd fds) = None.
Lemma rz_openat_dirref_lz : ltac2:(TCodec.tc2 tcn__DrvNodesLazyK "R3':'V6y8%211%411&SM&SKvV3vV0vUBr3%544321'E'6&S7r4%211(A%63521'O&T6r1&S5%33421'T5vV2(R2vUM&RDr2%211%411vUD%7221r6%;4L:21p0=1pYNB1&RAvU5%211%>11&S4&RF(R9%23651%421>%E261%H4Q9G1Q1&SFvU7vUL&SI%11Q>%554Q>3Q=1%M21G&T0r5%22H1%Q34QDQ241p0<1p0H1p0Q<1p0QD1pR6QK1pR4QL1p[HQN1").
Proof.
intros p KA KB Hp Hdr HA HB. cbv delta [post] in *.
assert (Hne : p <> []) by (intros ->; discriminate Hdr).
eapply srz_sys_lz; [exact Hh | exact HF | exact HE |].
eapply rz_open_lz; [exact Hh | exact open_copyins_nolazy | reflexivity | | | | exact Hfree | exact (fam_on_openat_ms segs scfg regs pc mem H17 Hfs_on) | |].
- intros eff. fold ms. rewrite (openat_check_head segs regs pc mem model H17 H10 Hfl), (path_at_cstr segs regs mem _ Hp).
rewrite (path_eqb_neq _ _ Hne), (path_is_dirref_no_slash _ Hdr), Hdr.
apply check_copyins_after_open_result.
- intros fd. cbv beta delta [fds]. rewrite with_fds_halted'. exact Hh.
- intros fd. cbv beta delta [fds]. apply with_fds_vm_lazy.
- intros e He. rewrite adv_set_epend. apply HA. exact He.
- rewrite adv_set_epend. exact HB.
Qed.
Lemma rz_openat_dot_lz : ltac2:(TCodec.tc2 tcn__DrvNodesLazyK "QF&SM&SKvV3vV0vUB&S8%544321'O&T6r1&S5%33421'T5vV2(R2vUM&RDr2%211%411vUD%7221r5%;4E:21p0=1pYNB1&RAvU5%211%>11&S4&RF(R9%23651%421>%E261r3%I4Q3H21&SFvU7vUL&SI%11Q8%554Q83Q71%N21H&T0r4%22I1%Q44Q>Q341p0<1p0I1p0Q=1pR6QD1pR4QE1").
Proof. intros KA KB Hp. apply (rz_openat_dirref_lz dot_path KA KB Hp). reflexivity. Qed.
Lemma rz_openat_file_lz : ltac2:(TCodec.tc2 tcn__DrvNodesLazyK "RK':'V6y8%211%411&SM&SKvV3vV0vUBr4%544321&G'Er5(<%11=%43=31%611'6&S6r6%211(A%;3521'=%11F&Q=&RMvUD%211r7%5221(4%12N=%F3931'O&T6r1&S5%33421'T5vV2(R2vUM&RDr2%211%411%621Dr8%:4Q<921p0<1pYNA1&RAvU5%211%=11&S4&RF(R;r9&V5yR0z%3221%6251%83<;1%:21Q7%J2<1%M4QOL1QA&SFvU7vUL&SI%11R4%554R43R31%Q221Q@&T0%12MQ@%Q74R9Q631p0;1p0M1p0Q@1p0QL1p0R31p0R;1pR6RB1pR4RC1pYJRE1p[HRF1").
Proof.
intros p d KA KB Hp Hne Hpl Hfs HA HB. cbv delta [post] in *.
eapply srz_sys_lz; [exact Hh | exact HF | exact HE |].
eapply rz_open_lz; [exact Hh | exact open_copyins_nolazy | reflexivity | | | | exact Hfree | exact (fam_on_openat_ms segs scfg regs pc mem H17 Hfs_on) | |].
- intros eff. fold ms. rewrite (openat_check_head segs regs pc mem model H17 H10 Hfl), (path_at_cstr segs regs mem p Hp).
rewrite (path_eqb_neq _ _ Hne), (openat_plain_name_noslash _ Hpl), (openat_plain_name_nodirref _ Hpl), Hfs.
apply check_copyins_after_open_result.
- intros fd. cbv beta delta [fds]. rewrite with_fds_halted'. exact Hh.
- intros fd. cbv beta delta [fds]. apply with_fds_vm_lazy.
- intros e He. rewrite adv_set_epend. apply HA. exact He.
- rewrite adv_set_epend. exact HB.
Qed.
End OpenatLz.
Lemma copy_iovecs_accesses_nolazy : ltac2:(TCodec.tc2 tcn__DrvNodesLazyK "Q@':'?'V6yR0%211%4211%611'=y8%711%311p071';&T:&T8&V9r1%22>1&T;+@&T<r2%211%5241%:271&T=+2+R0%3221%@251&S=r5r3%=11%@2?1%534>1&S<r6&RBr4%23981%5241p071p0>1pY4Q81pZHQ11p[<Q31pR8Q91").
Proof.
intros L mp k. induction k as [|k IH]; intros a0 Hw Hnl; cbn [copy_iovecs_accesses]; [apply acc_nolazy_nil|].
apply acc_nolazy_cons.
- intros j Hj. apply Hnl. lia.
- destruct (read_iovec_entry mp a0); try apply acc_nolazy_nil.
assert (Hu : bv_unsigned (a0 + 16) = (bv_unsigned a0 + 16)%Z).
{ rewrite bv_add_unsigned. change (bv_unsigned (16 : word)) with 16%Z. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
pose proof (u64_range a0). apply Z.mod_small. lia. }
apply IH; [rewrite Hu; lia|].
intros j Hj. rewrite Hu. replace (bv_unsigned a0 + 16 + j)%Z with (bv_unsigned a0 + (16 + j))%Z by ring. apply Hnl. lia.
Qed.
Lemma import_iovecs_accesses_nolazy : ltac2:(TCodec.tc2 tcn__DrvNodesLazyK "QE':'?'V6yR0%211%4211%611'=y8%711%311p071';&T9&T8&V9r2%22>1&T;+@&T<r1%211%5241%:271&R?%=221'IuQP0%22=1&S=r6r4r3%>11%A2@1%63541&S<r7&RIr5&V5%F1:%22Q81%53=41%8271p0:1p0B1p0F1pYFQ51pZDQ>1p[<Q81pR8Q>1").
Proof.
intros L mp iov cnt Hts Hc Hnl. unfold import_iovecs_accesses.
assert (Hwn : word_to_nat (Z_to_bv 64 (Z.of_nat cnt)) = cnt).
{ unfold word_to_nat. rewrite u64_lit by lia. apply Nat2Z.id. }
destruct (bv_eqb (Z_to_bv 64 (Z.of_nat cnt)) (Z_to_bv 64 1)) eqn:E1.
- apply bv_eqb_eq in E1. apply (f_equal bv_unsigned) in E1. rewrite !u64_lit in E1 by lia.
destruct (negb (access_okb iov 16)); [apply acc_nolazy_nil|].
apply (acc_nolazy_one L iov 16%nat (16 * Z.of_nat cnt) Hnl). lia.
- destruct (bv_eqb (Z_to_bv 64 (Z.of_nat cnt)) (Z_to_bv 64 0)); [apply acc_nolazy_nil|].
destruct (IOV_MAX <? bv_unsigned (Z_to_bv 64 (Z.of_nat cnt)))%Z; [apply acc_nolazy_nil|].
destruct (negb (access_okb iov (16 * bv_unsigned (Z_to_bv 64 (Z.of_nat cnt))))); [apply acc_nolazy_nil|].
rewrite Hwn. apply copy_iovecs_accesses_nolazy; [unfold TASK_SIZE in Hts; lia | exact Hnl].
Qed.
Lemma iov_prefix_accesses_nolazy : ltac2:(TCodec.tc2 tcn__DrvNodesLazyK "O':'?'V6yR0%211%4211%611';'K&S=r4&8r1%23991&V9&@%13<<4%32>1%93851qY<>1r2%=3@21&S<&RJr3%2215%42@1p061pZNE1pZFG1pR8H1").
Proof.
intros L iovs. induction iovs as [|[b n] r IH]; intros left HF.
- destruct left; apply acc_nolazy_nil.
- inversion HF as [|x l Hb Hr]; subst. cbn [fst snd] in Hb.
destruct left as [|l']; [apply acc_nolazy_nil|]. cbn [iov_prefix_accesses].
destruct (Nat.eqb (word_to_nat_bounded n (S l')) 0); [apply IH; exact Hr|].
apply acc_nolazy_cons; [|apply IH; exact Hr].
apply (nolazy_rng_sub L b (bv_unsigned n) _ Hb).
rewrite word_to_nat_bounded_eq_min. unfold word_to_nat. pose proof (u64_range n). lia.
Qed.
Lemma rz_writev_pending_lz : ltac2:(TCodec.tc2 tcn__DrvNodesLazyK "W5'QD'V6yR0%211'R='O':'?%1255%311y8%:11%611%711';&SMp021'E'=%118p0A1&QIr8%211&SIvV3%211%:3741%:1I&RNr7%211(2%11N%A3631&QJr:%211(4r9%22Q51%H3=41'R:%I11&RG&RL%117&V5%12Q>J%5231(R8%113%>2:1%Q43:41'D&T:z%221B&T=+2+O%3221%72G1%9261&V9r<%22R01+R2%QC3QO21&QGr>(3%3221r;%K2R81%QJ3R831r?u1%9221%QN3R<16r@u2%=221&T<&9%12R=<%311%Q82RE1%R73RE61'I%62RBI%22>1uQP0%4231%Q8231&T9&T8%Q12ROK&T;+@r=%A2RM1%C11%5241%8271&R?%;221&S@&QHrC%211%44RF1Q3Q9&SB%11Q5&SArE%811%34RL1Q5Q9&S=&ROrD%211rBrA%Q82SD1%Q:11%L2K1%93651'KrF%;11&8r1%23T2T21&@%13T4T43%R82T61%C3741qY<T21%;3T31A&T7%12T2C+1&RK%11H%QB231%31O+N%RJ2RI1%QF231%QM2R9Br2r5%R52T>1%R1231'T5vV2(R2&R0&QKrNr3%R?11%SD2U11%5241%711rL%:221rG%118%?4TA>31p0A1p0F1pZHTO1rJ%B291&SO&T4r4%211&T1&M'RE(R@%T92UF:%211&L&Jr6%S92UB1%S52QJ1%T92Q91q[@UB1%63UC1QM%83UG1Q:%>4UH=:1%R313%A221qZBC1%G2D1%Q=4U?Q<I1p0L1p0QE1p0QJ1tY>V0QO1p0R21p0R?1p0RJ1p0RO1p0S21p0S81p0SE1p0SL1p0T61p0T;1p0TC1p0TI1p0U41p0UA1p0UI1p0V11pY0V=1pYDVA1pZFVF1pZDVM1pZ:VL1p[:VN1p\HW01p[>W41").
Proof.
intros ms x8 model fd iov iovs bss T Hrom Hh Hsvc Hfd Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs Hnl1 Hnl2 bs
Ht1 Ht30 Hk.
destruct (writev_checkX segs ms x8 model fd iov iovs bss Hrom Hfd Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs
Ht1 Ht30)
as [Hlen Hchk]. fold bs in Hlen, Hchk.
set (tot := iovs_total iovs) in *.
set (CA := import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 (Z.of_nat (length iovs)))) in *.
assert (HnlA : forall k, acc_nolazy (m_vm_lazy model) (CA ++ iov_prefix_accesses iovs k)).
{ intros k. apply acc_nolazy_app; [apply import_iovecs_accesses_nolazy; [exact Hiok | lia | exact Hnl1] | apply iov_prefix_accesses_nolazy; exact Hnl2]. }
assert (Hnb : (1 <= length bs)%nat) by lia.
pose (effs := fun i : wr_index bs =>
mkEffectU (Z_to_bv 64 (Z.of_nat (proj1_sig i))) [] [] [] []
(CA ++ iov_prefix_accesses iovs (proj1_sig i))).
assert (Eacc : forall i, syscall_effect_accesses (effs i) = CA ++ iov_prefix_accesses iovs (proj1_sig i)).
{ intros i. unfold effs, syscall_effect_accesses. cbn [eff_copyins eff_writes write_accesses]. apply app_nil_r. }
assert (Enx : forall i : wr_index bs,
mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 (Z.of_nat (proj1_sig i))))) model
= mkCfg (advance_past_svc (apply_effect ms (effs i))) model).
{ intros [k Hk']. cbn [proj1_sig]. unfold effs. cbn [proj1_sig].
rewrite <- (apply_effect_copyins_no_write ms (Z_to_bv 64 (Z.of_nat k)) (CA ++ iov_prefix_accesses iovs k)).
reflexivity. }
apply (srz_node segs scfg (mkCfg ms model) (wr_index bs)
(fun i => map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs))
(fun i => mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 (Z.of_nat (proj1_sig i))))) model)
(fun i => T (proj1_sig i)) (wr_full bs Hnb)).
2:{ intros [k [Hk1 Hk2]]. cbn [proj1_sig]. apply Hk; assumption. }
assert (Hku : forall k, (k <= length bs)%nat -> bv_unsigned (Z_to_bv 64 (Z.of_nat k)) = Z.of_nat k).
{ intros k Hk2. apply u64_lit. lia. }
apply (node_ok_of_pnode_sysno segs scfg ms model x8 66%Z); [exact Hsvc | exact Hno | exact injected_arm_66 |].
split.
- intros i. rewrite Enx. apply (sstep_of_check_mat ms model x8); [exact Hh | exact Hsvc | | exact Hh | rewrite Eacc; apply HnlA].
destruct i as [k [Hk1 Hk2]]. unfold effs. cbn [proj1_sig]. rewrite Hchk.
rewrite (Hku k Hk2), Nat2Z.id.
rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia.
replace (addr_is_error_b (Z_to_bv 64 (Z.of_nat k))) with false
by (symmetry; unfold addr_is_error_b, two_pow_64; apply Z.ltb_ge; rewrite (Hku k Hk2); lia).
rewrite (proj2 (access_ranges_eqb_eq _ _) eq_refl). reflexivity.
- assert (Hinv : forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
exists i : wr_index bs, eff = effs i /\ m' = model /\ ev = map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs)).
{ intros [ret ws zs us cs ci] m' ev Hc. rewrite Hchk in Hc.
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
destruct cs; [|discriminate].
destruct ((1 <=? bv_unsigned ret)%Z && (bv_unsigned ret <=? tot)%Z && negb (addr_is_error_b ret))%bool eqn:Eb;
[|discriminate].
destruct (access_ranges_eqb ci (CA ++ iov_prefix_accesses iovs (Z.to_nat (bv_unsigned ret)))) eqn:Eci;
[|discriminate].
injection Hc as <- <-.
apply andb_true_iff in Eb as [Eb _]. apply andb_true_iff in Eb as [E1 E2].
apply Z.leb_le in E1. apply Z.leb_le in E2. apply access_ranges_eqb_eq in Eci.
assert (Hkr : (1 <= Z.to_nat (bv_unsigned ret))%nat /\ (Z.to_nat (bv_unsigned ret) <= length bs)%nat) by lia.
exists (exist _ (Z.to_nat (bv_unsigned ret)) Hkr). cbn [proj1_sig]. unfold effs. cbn [proj1_sig].
rewrite Z2Nat.id by lia. rewrite u64_roundtrip'. subst ci. repeat split; reflexivity. }
intros e st Hss.
destruct (sstep_svc_inv segs ms model x8 e st Hsvc Hss)
as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hmat & ->) | [(Hh2 & -> & Hmat & ->) | (code & Hh2 & -> & ->)]])
| (eff & Hc & -> & ->)].
+ destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
rewrite Eacc, (mat_id_of_nolazy _ _ (HnlA _)) in Hmat. injection Hmat as <-.
exists i. rewrite Enx. split; reflexivity.
+ destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
rewrite Eacc, (mat_id_of_nolazy _ _ (HnlA _)) in Hmat. discriminate.
+ destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). congruence.
+ exfalso. rewrite Hchk in Hc. destruct eff as [ret ws zs us cs ci].
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
destruct cs; [|discriminate]. destruct (_ && _)%bool; [destruct (access_ranges_eqb _ _)|]; discriminate.
Qed.
Lemma rz_writev2_lz : ltac2:(TCodec.tc2 tcn__DrvNodesLazyK "XG&S9y5'V6yR0%211%5241'=y8%611%311p061'R=yQ0%;11'O':%118';&SMp021'E%?18&QAvV3r=%3221(4r:%22?1%93841'6&QBr;%211(A%?3521%N1Q0&RN%11>(2%11Q4%E3531'R:%Q511&RG&RLr>%211&V5r<%22Q?1%7241(R8%113%L2<1%Q33<41'D&T:z%221Q3&T=+2+O%3221%72Q81%9261&SErC(V4+A(C%33R621%6251+R2%J2R71%QG3R731rD+:%:3R=18%=231r?%Q12R>1%QN3R>31rE+;%A3RD1?%D231%R33RC17rF+<%F3RI1D%I231%Q<2RIO%R93RI21%RH1R>&SGrAu8%34R;?21&QNr@%2241%R<2RF1%RC3951&T8&V9rB%22S81+8%5221%QN2S;1%@4RHG1>%RL3B1:rG%92S?Q?+@%<221%R52SB1%G4RO51E%S33I1ArH%@2SFQ=+H%C221%R<2SI1%N4S651L%S:3Q01HrI&Q5%11QN%Q34S;3QF1%S92SCO%S@3Q621rJ%61L%Q84S@2R41%SD3Q:15&T9%Q12T7I+Q0%Q4221&R?%5221%Q62T<QG%Q8261%8214%Q92T?QO%Q;241%;217&S=&ROrM%211%431D>rN%511%QC2TIM%832H1rO%911%QG2TMQ8%<32Q21+1rK%QK2U11%QM219%M241rL%QO2U51%R02U6Q4%R2221+N%S@2S?1%Q4231'Iu1r1%3221r2&9&5%13U=>B%32U>1%9251'T5vV2(R2&SFvU7&SHrQ8&T<r3%211%TB2UO1%635SE1&SJrQ7+4%3221rQ6&SI%11UC%@5?8431rQ5%C221%Q;1>%G4UHF21p0I1p0Q01pZHV11rQ4%I5H<81:rQ3%L221&SO&T4%Q53VAQFRD%211&T1&M'RE(R@rQ2%U@2VM1%311&L&J%Q@3VLR=QM%QB2VM1%QH2QF1%U?2QF1q[@VG1%63VH1QI%83W21QE%?4W3>:1%S713%B221qZBD1%H2E1%QH4VIQGJ1p0O1p0R51p0R=1p0RC1p0RH1p0RM1p0S31p0S71p0S;1p0SB1p0SG1p0SN1p0T61p0T>1p0TH1p0U31p0U:1p0U@1p0UH1p0V31p0V>1p0VM1p0W41p0W;1pY0WF1pYBWJ1pY@WK1p[DX81pY:X91p[BX:1pY8X;1pZDX<1pZ:X31p\FX51p[:X81p[6X:1p[JXA1p\2XA1").
Proof.
intros regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2 T HF HE Hh Hfd Hfdr H17 H10 H11 H12
Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Hiok Hb1 Hb2 Nl0 Nl1 Nl2 Ht1 Ht30 Hk.
eapply srz_sys_lz; [exact Hh | exact HF | exact HE |].
pose proof (u64_range n1). pose proof (u64_range n2).
replace (bs1 ++ bs2) with (concat [bs1; bs2]) in * by (cbn; rewrite app_nil_r; reflexivity).
eapply (rz_writev_pending_lz (epend regs pc mem (seg_rom segs) (getr regs 17)) (getr regs 17) model fd iov
[(b1, n1); (b2, n2)] [bs1; bs2] T);
[reflexivity | exact Hh | reflexivity | exact Hfd | exact Hfdr
| rewrite H17; apply u64_lit; lia
| rewrite ms_gpr_epend0; exact H10 | rewrite ms_gpr_epend1; exact H11 | rewrite ms_gpr_epend2; exact H12
| cbn; lia | change (Z.of_nat (length [(b1, n1); (b2, n2)])) with 2%Z; lia
| | cbn [iov_bufs_ok]; repeat split; assumption |
| change (16 * Z.of_nat (length [(b1, n1); (b2, n2)]))%Z with 32%Z; exact Nl0
| repeat constructor; assumption
| cbn [iovs_total]; lia
| cbn [iovs_total]; lia | ].
- cbn [iov_array ms_mem epend].
replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16)) + 8)) with (Z_to_bv 64 (bv_unsigned iov + 24)).
2:{ change (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16)) + 8)) with (at_ (at_ iov 16) 8).
rewrite at_at. reflexivity. }
repeat split; try assumption; lia.
- cbn [iov_bufs ms_mem epend]. repeat split; assumption.
- intros k Hk1 Hk2. rewrite adv_set_epend. apply Hk; assumption.
Qed.
Lemma rz_writev1_lz : ltac2:(TCodec.tc2 tcn__DrvNodesLazyK "W>&S9y5'V6yR0%211%5241'=y8%611%311p061'R=yQ0%;11'O':%118';&SMp021'E%?18&QAvV3r:%3221(4r7%22?1%93841'6&QBr8%211(A%?3521%N1Q0&RN%11>(2%11Q4%E3531'R:%Q511&RG&RLr;%211&V5r9%22Q?1%7241(R8%113%L2<1%Q33<41'D&T:z%221Q3&T=+2+O%3221%72Q81%9261&SEr@(V4+A(C%33R621%6251+R2%J2R71%QG3R731rA+:%:3R=18%=231r<%Q12R>1%QN3R>31rB+;%A3RD1?%D231%R33RC17rC+<%F3RI1D%I231+1%Q=2RJ1%R:3RJ31%RI1R?&SGr>u8%34R<@21&QNr=%2241%R=2RG1%RD3951&T8&V9r?%22S91+8%5221%QO2S<1%@4RIH1>%RM3B1:rD&Q5%11C%E4RN3:1%RL2S6A%S33H21&T9%?2SFQ=+@%B221&R?%5221%D2SKQK%F261%8214&S=&ROrF%211%431Q=;rG%511%N2T5QE%832QA1%Q02T7QB%C2Q?1%Q22T9J+N%RB2RA1%G231'Iu1r1%3221r2&9%12T>C%7231'T5vV2(R2&SFvU7&SHrQ0&T<r3%211%SB2TO1%635RE1&SJrO+4%3221rN&SI%11TC%@5?8431rM%C221%Q;1>%G4THF21p0I1p0N1pZHU11rL%I5H<81:rK%L221&SO&T4rE%211&T1&M'RE(R@rJ%T@2UM1%311&L&J%Q?2ULQN%QE2QC1%T>2QC1q[@UF1%53UG1QF%73V11R6%>4V2=91%B13%A221qZBC1%G2D1%QG4UHQFI1p0N1p0R21p0R71p0R:1p0R?1p0RE1p0RI1p0S01p0S71p0SA1p0SL1p0T41p0T:1p0TB1p0TM1p0U81p0UG1p0UN1p0V51pY0V@1pY@VD1p[BW11pY8W21pZDW31pZ:VJ1p\FVL1p[:VO1p[6W11p[JW81p\2W81").
Proof.
intros regs pc mem model w fd iov b1 n1 bs1 T HF HE Hh Hfd Hfdr H17 H10 H11 H12
Rb1 Rn1 Rs1 Hiok Hb1 Nl0 Nl1 Ht1 Ht30 Hk.
eapply srz_sys_lz; [exact Hh | exact HF | exact HE |].
pose proof (u64_range n1).
replace bs1 with (concat [bs1]) in Hk by (cbn; rewrite app_nil_r; reflexivity).
replace bs1 with (concat [bs1]) by (cbn; rewrite app_nil_r; reflexivity).
eapply (rz_writev_pending_lz (epend regs pc mem (seg_rom segs) (getr regs 17)) (getr regs 17) model fd iov
[(b1, n1)] [bs1] T);
[reflexivity | exact Hh | reflexivity | exact Hfd | exact Hfdr
| rewrite H17; apply u64_lit; lia
| rewrite ms_gpr_epend0; exact H10 | rewrite ms_gpr_epend1; exact H11 | rewrite ms_gpr_epend2; exact H12
| cbn; lia | change (Z.of_nat (length [(b1, n1)])) with 1%Z; lia
| | cbn [iov_bufs_ok]; split; [assumption | exact I] |
| change (16 * Z.of_nat (length [(b1, n1)]))%Z with 16%Z; exact Nl0
| repeat constructor; assumption
| cbn [iovs_total]; lia
| cbn [iovs_total]; lia | ].
- cbn [iov_array ms_mem epend]. repeat split; try assumption; lia.
- cbn [iov_bufs ms_mem epend]. split; [assumption | exact I].
- intros k Hk1 Hk2. rewrite adv_set_epend. apply Hk; assumption.
Qed.
Lemma rz_writev2_wall_lz : ltac2:(TCodec.tc2 tcn__DrvNodesLazyK "XA&S9y5'V6yR0%211%5241'=y8%611%311p061'R=yQ0%;11'O':%118&SM'E%=16&QAvV3r=%3221(4r:%22=1%93841'6&QBr;%211(A%?3521%L1N&RN%11>(2%11Q2%E3531'R:%Q311&RG&RLr>%211&V5r<%22Q=1%7241(R8%113%L2<1%Q33<41'D&T:z%221Q3&T=+2+O%3221%72Q81%9261&SErC(V4+A(C%33R421%6251+R2%J2R51%QG3R531rD+:%:3R;18%=231r?%Q12R<1%QN3R<31rE+;%A3RB1?%D231%R33RA17rF+<%F3RG1D%I231%Q<2RGO%R93RG21%RF1R<&SGrAu8%34R;?21&QNr@%2241%R<2RD1%RC3951&T8&V9rB%22S61+8%5221%QN2S91%@4RHG1>%RL3B1:rG%92S=Q?+@%<221%R52S@1%G4RO51E%S33I1ArH%@2SDQ=+H%C221%R<2SG1%N4S651L%S:3Q01HrI&Q5%11QN%Q34S;3QF1%S92SAO%S@3Q621rJ%61L%Q84S@2R41%SD3Q:15&T9%Q12T5I+Q0%Q4221&R?%5221%Q62T:QG%Q8261%8214%Q92T=QO%Q;241%;217&S=&ROrM%211%431D>rN%511%QC2TGM%832H1rO%911%QG2TKQ8%<32Q21+1rK%QK2TO1%QM219%M241rL%QO2U31%R02U4Q4%R2221+N%S@2S?1%Q4231(<'RE%211%QI11';'Iu1r1%3221r2&9&5%13U@Q3C%32UA1%9251'T5vV2(R2&SFvU7&SHrQ9&T<r3%211%TG2V21%635SJ1&SJrQ8+4%3221rQ7&SI%11UH%@5?8431rQ6%C221&T1&M(R@rQ4%U72VB1%311&N%Q13V@R0R3%23VAF1%84VBQ=41%:21QF%Q14V7Q0<1p0Q31p0Q:1pZHQ?1rQ5%Q35Q2FB1D%Q521>rQ2%UF2W11%B11%Q?3VNR1R5%E4VOQJ21%G21S5%Q>4VDQ=71p0;1p0QL1p0R11p0R91p0R?1p0RD1p0RI1p0RO1p0S31p0S71p0S>1p0SC1p0SJ1p0T21p0T:1p0TD1p0TO1p0U61p0U<1p0UD1p0UO1p0V:1p0VI1p0W01p0W71pR2WB1pYBWD1pY@WE1p[DX21pY:X31p[BX41pY8X51pZDX61pZ:WM1p\FWO1p[:X21p[6X41p[JX;1p\2X;1").
Proof.
intros regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2 K HF HE Hh Hfd Hfdr H17 H10 H11 H12
Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Hiok Hb1 Hb2 Nl0 Nl1 Nl2 Ht1 Ht30 HK Hk.
pose proof (rdn_length segs mem _ _ _ Rs1) as L1. pose proof (rdn_length segs mem _ _ _ Rs2) as L2.
pose proof (u64_range n1). pose proof (u64_range n2).
apply rz_wall; [rewrite length_app; unfold word_to_nat in L1, L2; lia | exact HK |].
eapply (rz_writev2_lz regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2
(fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs1 ++ bs2))) K)); eassumption.
Qed.
Lemma rz_writev1_wall_lz : ltac2:(TCodec.tc2 tcn__DrvNodesLazyK "W9&S9y5'V6yR0%211%5241'=y8%611%311p061'R=yQ0%;11'O':%118&SM'E%=16&QAvV3r:%3221(4r7%22=1%93841'6&QBr8%211(A%?3521%L1N&RN%11>(2%11Q2%E3531'R:%Q311&RG&RLr;%211&V5r9%22Q=1%7241(R8%113%L2<1%Q33<41'D&T:z%221Q3&T=+2+O%3221%72Q81%9261&SEr@(V4+A(C%33R421%6251+R2%J2R51%QG3R531rA+:%:3R;18%=231r<%Q12R<1%QN3R<31rB+;%A3RB1?%D231%R33RA17rC+<%F3RG1D%I231+1%Q=2RH1%R:3RH31%RG1R=&SGr>u8%34R<@21&QNr=%2241%R=2RE1%RD3951&T8&V9r?%22S71+8%5221%QO2S:1%@4RIH1>%RM3B1:rD&Q5%11C%E4RN3:1%RL2S4A%S33H21&T9%?2SDQ=+@%B221&R?%5221%D2SIQK%F261%8214&S=&ROrF%211%431Q=;rG%511%N2T3QE%832QA1%Q02T5QB%C2Q?1%Q22T7J+N%RB2RA1%G231(<'RE%211%QK11';'Iu1r1%3221r2&9%12TAE%7231'T5vV2(R2&SFvU7&SHrQ1&T<r3%211%SG2U21%635RJ1&SJrQ0+4%3221rO&SI%11TH%@5?8431rN%C221&T1&M(R@rL%T72UB1%311&NrH%23UAF1%84UBQ;41%:21QG%Q14U7Q0<1p0Q31p0Q81pZHQ=1rM%Q35Q2FB1D%Q521>rJ%TF2V11%B11%D4UNQG1R5rE%G221%Q>4UDQ=71p0;1p0QJ1p0QO1p0R41p0R71p0R<1p0RB1p0RF1p0RM1p0S41p0S>1p0SI1p0T11p0T71p0T?1p0TJ1p0U51p0UD1p0UK1p0V21pR2V=1pY@V?1p[BVL1pY8VM1pZDVN1pZ:VE1p\FVG1p[:VJ1p[6VL1p[JW31p\2W31").
Proof.
intros regs pc mem model w fd iov b1 n1 bs1 K HF HE Hh Hfd Hfdr H17 H10 H11 H12
Rb1 Rn1 Rs1 Hiok Hb1 Nl0 Nl1 Ht1 Ht30 HK Hk.
pose proof (rdn_length segs mem _ _ _ Rs1) as L1. pose proof (u64_range n1).
apply rz_wall; [unfold word_to_nat in L1; lia | exact HK |].
eapply (rz_writev1_lz regs pc mem model w fd iov b1 n1 bs1
(fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs1)) K)); eassumption.
Qed.
Lemma rz_writev2_ch_lz : ltac2:(TCodec.tc2 tcn__DrvNodesLazyK "X1&S9y5'V6yR0%211%5241'=y8%611%311p061'R=yQ0%;11'O':%118&SM'E%=16&QAvV3r=%3221(4r:%22=1%93841'6&QBr;%211(A%?3521%L1N&RN%11>(2%11Q2%E3531'R:%Q311&RG&RLr>%211&V5r<%22Q=1%7241(R8%113%L2<1%Q33<41'D&T:z%221Q3&T=+2+O%3221%72Q81%9261&SErC(V4+A(C%33R421%6251+R2%J2R51%QG3R531rD+:%:3R;18%=231r?%Q12R<1%QN3R<31rE+;%A3RB1?%D231%R33RA17rF+<%F3RG1D%I231%Q<2RGO%R93RG21%RF1R<&SGrAu8%34R;?21&QNr@%2241%R<2RD1%RC3951&T8&V9rB%22S61+8%5221%QN2S91%@4RHG1>%RL3B1:rG%92S=Q?+@%<221%R52S@1%G4RO51E%S33I1ArH%@2SDQ=+H%C221%R<2SG1%N4S651L%S:3Q01HrI&Q5%11QN%Q34S;3QF1%S92SAO%S@3Q621rJ%61L%Q84S@2R41%SD3Q:15&T9%Q12T5I+Q0%Q4221&R?%5221%Q62T:QG%Q8261%8214%Q92T=QO%Q;241%;217&S=&ROrM%211%431D>rN%511%QC2TGM%832H1rO%911%QG2TKQ8%<32Q21+1rK%QK2TO1%QM219%M241rL%QO2U31%R02U4Q4%R2221+N%S@2S?1%Q4231';'Iu1r1%3221r2&9&5%13U<?C%32U=1%9251'T5vV2(R2&SFvU7&SHrQ8&T<r3%211%TC2UN1%635SF1&SJrQ7+4%3221rQ6&SI%11UD%@5?8431rQ5%C221%F4UHE1Q<p0H1p0O1pZHQ41rQ4%H5G;719rQ3%K221&T3rQ1%U92VD1%Q53V@QGRE%4321RL%Q34V5Q261p0;1p0QA1p0QI1p0QO1p0R41p0R91p0R?1p0RC1p0RG1p0RN1p0S31p0S:1p0SB1p0SJ1p0T41p0T?1p0TF1p0TL1p0U41p0U?1p0UJ1p0V91p0V@1p0VG1pR2W21pYBW41pY@W51p[DWB1pY:WC1p[BWD1pY8WE1pZDWF1pZ:W=1p\FW?1p[:WB1p[6WD1p[JWK1p\2WK1").
Proof.
intros. unfold t_write_ch.
eapply (rz_writev2_lz regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2 (fun _ => K)); eassumption.
Qed.
Lemma rz_writev1_zero_lz : ltac2:(TCodec.tc2 tcn__DrvNodesLazyK "U>&S9y5'V6yR0%211%5241'=y8%611%311p061'R=yQ0%;11'O&SM'E%;14&QAvV3r8%3221(4r5%22;1%93841'6&QBr6%211(A%?3521%J1L&RN%11>(2%11Q0%E3531'R:%Q111&RG&RLr9%211&V5r7%22Q;1%7241(R8%113%L2<1%Q33<41'D&T:z%221Q3&T=+2+O%3221%72Q81%9261&SEr>(V4+A(C%33R221%6251+R2%J2R31%QG3R331r?+:%:3R918%=231r:%Q12R:1%QN3R:31r@+;%A3R@1?%D231%R33R?17rA+<%F3RE1D%I231+1%Q=2RF1%R:3RF31':%11RD%RG11&SGr<u8%34R>B21&QNr;%2241%R?291%RF3951&T8&V9r=%22S71+8%5221%R12S:1%@4RKJ1>%R32S<QI%>2@1%RK2E1%S23E41&T9%<2SAQE+@%?221&R?%5221%6252&S=&ROrC%211%431Q?9'T5vV2(R2&SFvU7&SHrG%231QLG&SJrF+4%3221rE&SI%11SJ%<5;8431rD%?221%B4SNA1R9rH%A5@1>;6%C219%F4T2E1R6p051p0I1p0O1p0Q11p0Q81p0QE1p0R21p0R:1p0R@1p0RH1p0S31p0S>1p0SM1p0T41p0T;1pR2TF1pY8U21pZDU31pZ:TJ1p\FTL1p[:TO1p[6U11p[JU81p\2U81").
Proof.
intros regs pc mem model w fd iov b1 K HF HE Hh Hfd Hfdr H17 H10 H11 H12 Rb1 Rn1 Hiok Hb1 Nl0 Hc.
eapply srz_sys_lz; [exact Hh | exact HF | exact HE |].
set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
assert (Hno : bv_unsigned (getr regs 17) = 66%Z) by (rewrite H17; apply u64_lit; lia).
assert (Harr : iov_array segs (ms_mem ms) iov [(b1, Z_to_bv 64 0)]).
{ cbn [iov_array ms_mem ms epend]. refine (conj Rb1 (conj Rn1 (conj _ I))). rewrite u64_lit by lia. lia. }
assert (Himp : import_iovecs (ms_read_byte ms) iov (Z_to_bv 64 1) = ImpOk [(b1, Z_to_bv 64 0)]).
{ unfold import_iovecs. rewrite (proj2 (bv_eqb_eq _ _) eq_refl).
rewrite (access_okb_of_le iov 16) by lia.
rewrite (read_iovec_entry_of_array segs ms b1 (Z_to_bv 64 0) [] iov eq_refl Harr).
rewrite u64_lit by lia. change (Z.min 0 MAX_RW_COUNT) with 0%Z.
rewrite (access_okb_of_le b1 0) by lia. reflexivity. }
assert (Hacc : import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 1) = [(iov, 16%nat)]).
{ unfold import_iovecs_accesses. rewrite (proj2 (bv_eqb_eq _ _) eq_refl).
rewrite (access_okb_of_le iov 16) by lia. reflexivity. }
eapply (rz_ret_only_copyins_silent_lz ms model (getr regs 17) [(iov, 16%nat)] (Z_to_bv 64 0) model);
[exact Hh | reflexivity | | exact Hh | apply (acc_nolazy_one _ _ _ 16 Nl0); lia | unfold ms; rewrite adv_set_epend; exact Hc].
intros eff.
rewrite (check_syscall_writev (sys_input segs ms (getr regs 17)) eff model) by (rewrite in_sysno_si; exact Hno).
rewrite in_arg0_si, in_arg1_si, in_arg2_si.
assert (G0 : ms_gpr ms 0 = Z_to_bv 64 fd) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
assert (G1 : ms_gpr ms 1 = iov) by (unfold ms; rewrite ms_gpr_epend1; exact H11).
assert (G2 : ms_gpr ms 2 = Z_to_bv 64 1) by (unfold ms; rewrite ms_gpr_epend2; exact H12).
rewrite G0, G1, G2.
rewrite fd32_id by (rewrite u64_lit; lia).
unfold check_writev. rewrite Hfd.
replace (w_is0 (Z_to_bv 64 fd)) with false by (symmetry; apply w_is0_pos; rewrite u64_lit; lia).
change (iovcnt32 (Z_to_bv 64 1)) with (Z_to_bv 64 1).
rewrite in_mem_si, Himp, Hacc.
unfold cap_iovecs. cbn [cap_iovecs_aux iovs_total].
change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.min_r by (unfold MAX_RW_COUNT; lia).
change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. cbv beta iota zeta.
change ((0 + 0 =? 0)%Z) with true. cbv beta iota. reflexivity.
Qed.
Lemma rz_exit_at_lz : ltac2:(TCodec.tc2 tcn__DrvNodesLazyK "RI&S9y5'V6yR0%211%5241'=y8%611%311p061'R=yQ0%;11'E%912&QAvV3r6%3221(4r2%2291%93841'6&QBr3%211(A%?3521%H1J&RNr5%211(2%11O%F3631'H&SEr:(V4+A(C%33Q:21%6251&V5+RN%22Q<1%Q23Q<41+RM%52Q?1%Q53Q?71%?241r;+:%?3QF1=%B231%Q;3QE1I'T5vV2(R2&SFvU7r<r9%4532<J1r8%7221&T2&V8+WO%J2R41%33R5QF1&RM%118%7231%B4QKA91p0D1p0J1p0Q;1p0QC1p0QJ1pYHR>1p\FR61p[:R91p\4R;1p[6R<1p[JRC1p\2RC1").
Proof.
intros regs pc mem rom model w code HF HE Hh H17 H10.
eapply srz_sys_lz; [exact Hh | exact HF | exact HE |].
rewrite <- H10, <- (ms_gpr_epend0 regs pc mem rom (getr regs 17)).
eapply srz_exit; [exact Hh | reflexivity |].
destruct H17 as [H|H]; [right|left]; rewrite H; reflexivity.
Qed.
Lemma rz_exit_at_lit_lz : ltac2:(TCodec.tc2 tcn__DrvNodesLazyK "S2&S9y5'V6yR0%211%5241'=y8%611%311p061'R=yQ0%;11'O'E%:13&QAvV3r6%3221(4r2%22:1%93841'6&QBr3%211(A%?3521%I1K&RNr5%211(2%11Q0%F3631'H&SEr:(V4+A(C%33Q;21%6251&V5+RN%22Q=1%Q23Q=41+RM%52Q@1%Q53Q@71%?241r;+:%?3QG1=%B231%<2QGI%Q<3QG21'D&T9z%221Q<&T:+X0%22Q?1%7241'T5vV2(R2&SFvU7r=r<%45321EQ3r9%7221&T2r7%Q22R=1&RM%116%5231%@4R2?71p0B1p0K1p0Q21p0QC1p0QK1p0R21pYHR=1p\FR?1p[:RB1p\4RD1p[6RE1p[JRL1p\2RL1").
Proof.
intros regs pc mem rom model w code HF HE Hh H17 H10 Hc.
rewrite <- (bv_and_255_small code Hc). eapply rz_exit_at_lz; eassumption.
Qed.
End WithSegs.
End FPX_1.
