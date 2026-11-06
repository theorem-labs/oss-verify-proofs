(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import RunEnv
PropExec CatExec CatSim SeqExec StoreOk ShapeAlg DivergeSim SpinAlg SpinAlgX Nodes Hoare Frame
MmapSim AllocSim FileSim AgentLib ArgvEnv MuslStrlen RefLayout
SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4
Spec LibWritev RefNodes Js0ExitBase Js0Exit RefMemcpyLib Js0MemcpyBase Js0Memcpy Js0Memchr Js0Strnlen
Js0Startup Js0StartupFacts Js0MainEntry LibTail.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import Js0OpenFail_defs Js0OpenFail_tail Js0OpenFail_tail2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Js0OpenFail () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Fs."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0MainEntry."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0OpenFail.FPX_1.OpenFail."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0OpenFail_defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Spec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymRun."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1O"; "1Some"; "1app"; "1bool"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1prod"; "1true"; "2I"; "2and"; "2eq"]; ["2ex"; "2not"; "3add"; "4le"; "5Z"; "6Fs"; "6fs_lookup"; "7mkCfg"; "8FdChannel"; "8FdEntry"; "8errno_ret"; "8fd_lookup"; "8m_fds"; "8m_fs"; "8m_halted"; "8m_vm_lazy"]; ["9open_ignored_flags"; "9openat_errnos"; "9openat_plain_name"; ":AT_FDCWD"; ";bvmap"; "0M"; "0R"; "<p1"; "=ENV"; "=model0"; ">knA"; ">srA"; "?getr"; "?mkst"; "?rdn"; "?regupd"]; ["?seg_rom"; "?v_addi"; "@TSet"; "Amsg_cannot_open"; "At_die"; "Bsrealizes"; "CEVar"; "Cridx"; "Csr_upd"; "Dknow_ok"; "Dregs_ok"; "Evals_ev"; "Floaded_segments"; "GIn"; "Hadd"; "Hldiff"]; ["Hle"; "Hof_nat"; "Hpow"; "Hsub"; "0T"; "0a0s"; "0e"; "0envv"; "0fs0"; "0fx"; "0mem0"; "0path"; "0regs0"; "0scfg"; "0sp0"; "IBV"]; ["IZ_to_bv"; "Ibv"; "Ibv_unsigned"; "0t8"; "0vals"; "0x"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Lemma errno_ret_range : ltac2:(TCodec.tc2 tcn__Js0OpenFail "H'D'>&R0+1r1%3221+SoO%5231%7231&R3&R2+2+R0%3221%5218&RByR0&Jr2%211%5241%C271p0>1pT>G1").
Proof. intros e He. unfold errno_ret. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
replace ((- e) mod 2 ^ 64)%Z with (2 ^ 64 - e)%Z; [lia|].
apply Z.mod_unique with (q := (-1)%Z); lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
Lemma In_firstn : forall {A} (l : list A) n x, In x (firstn n l) -> In x l.
Proof.
intros A l n x H. rewrite <- (firstn_skipn n l). apply in_app_iff. left. exact H.
Qed.
Lemma openat_errnos_range : ltac2:(TCodec.tc2 tcn__Js0OpenFail "?'D&QMr1&Q1%33421'>&R0+1r2%3221+SoO%5231%7231p091pT>>1").
Proof.
intros e He. unfold openat_errnos in He. cbn in He.
unfold ENOMEM, EACCES, EMFILE, ENFILE in He. lia.
Qed.
Section OpenFail.
Context {RE : RunEnv}.
Variable sp0 : word.
Variables a0s path : list byte.
Variable envv : list (list byte).
Variable uid : word.
Variable hw : word.
Variable rdraw : EntryDraw.
Variable tid : word.
Variable regs0 : bvmap 5 word.
Variable mem0 : word -> option byte.
Variable brk : word.
Variable mbase : word.
Variable fs0 : Fs.
Variable stdin0 : InputStream.
Variable lim : Z.
Hypothesis Hva : valid_argv [a0s; path].
Hypothesis Hve : valid_envp envv.
Hypothesis Hvsp : valid_sp sp0.
Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
Hypothesis ME : main_entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0.
Hypothesis Hfits : entry_stack_fits sp0 [a0s; path] envv.
Hypothesis Hfs : sc_fs scfg = true.
Definition ENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev (blobs0 a0s path hw rdraw)).
Definition model0 : Model :=
mkModelE fds_init (mkVmMapsFull (segments_reserved RSEGS) [] [] brk brk lim mbase sp0) stdin0 fs0 None (Some tid) None.
Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
Lemma model0_halted : ltac2:(TCodec.tc2 tcn__Js0OpenFail "<'?':'RAyR0%211%411&N&Q9%211(0%116%;3631").
Proof. reflexivity. Qed.
Lemma model0_lazy : ltac2:(TCodec.tc2 tcn__Js0OpenFail ">'?'7';'RAyR0%211%4211%611&O&Q9%211(9%116%=3631").
Proof. reflexivity. Qed.
Lemma model0_fd2 : ltac2:(TCodec.tc2 tcn__Js0OpenFail "B'?':'I%211&K&L&Q9%211&R@yR0+2%3221%8251(2(H%114%32>1%A3>51").
Proof. reflexivity. Qed.
Lemma model0_fs : ltac2:(TCodec.tc2 tcn__Js0OpenFail "7'?&E&M&Q9%211vR8%63521").
Proof. reflexivity. Qed.
Lemma path_nonul : ltac2:(TCodec.tc2 tcn__Js0OpenFail ";&A&QM'RAy8%211&R@z%2241vR;%83521%:11").
Proof.
destruct Hva as (_ & _ & _ & Hn & _). inversion Hn as [|x l Hx Hl]; subst. inversion Hl; subst. assumption.
Qed.
Lemma path_len : ltac2:(TCodec.tc2 tcn__Js0OpenFail ";&R0&R1&6'RAy8%211vR;%5221%711+SooO%:221").
Proof.
destruct Hva as (_ & _ & Hl & _ & _). inversion Hl as [|x l Hx Hl']; subst. inversion Hl'; subst. assumption.
Qed.
Lemma path_facts : ltac2:(TCodec.tc2 tcn__Js0OpenFail "R2'>'?':'7'RAy8%211%411%611&Q>&QLvR:&Q7vR>vR5vR;vR7%544321&B&6%12>5u1%4221%>4=<61(2&3(5&R@z%22H1(9%11I%63J31%83KB1%:2K1%Q23K<1&R0&RByR0%221J%322G%5221&QN+RPZUH%2251%9251&R1%11K%6281+A%8221+TPPPPPPPP0%@221'@%K2@6u8%Q?4Q>Q=21r1%Q22QC1%QJ3QC31qU8QE1%82QF1%QN2:1%QO2B1%R02G1%R12N1").
Proof.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.
destruct (main_str sp0 a0s path envv uid hw rdraw tid regs0 mem0 Hva Hve Hvsp ME 1%nat ltac:(lia)) as (Sr & Slo & Shi & Slen).
pose proof (main_str_fits sp0 a0s path envv uid hw rdraw Hva Hve Hvsp Hfits 1%nat ltac:(lia)) as Sfit.
cbn [nth] in Sr, Slo, Shi, Slen, Sfit. unfold p1.
split; [exact Sr|]. split; [exact Slo|]. split; [exact Shi|]. split; [exact Sfit|].
pose proof (lay_bsb_nw RPH sp0 rdraw [a0s; path] envv uid hw Hva Hve ltac:(unfold sp_window_hi; lia)) as Hnw.
destruct (read_word_stack RPH RSEGS sp0 [a0s; path] envv 1 (length path) uid hw rdraw ltac:(cbn; lia) ltac:(cbn; lia) Hnw)
as (t8 & Hl8 & Hr8).
exists t8. rewrite w_add_nat in Hr8.
pose proof (u64_range (cat_argv_ptr sp0 [a0s; path] envv 1)).
rewrite (main_entry_rdn_above sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0 ME) by (rewrite u_small by lia; lia).
pose proof (rdn_wmem_stack RSEGS RPH sp0 [a0s; path] envv uid hw rdraw) as Hw. unfold wmem in Hw.
rewrite Hw by (rewrite u_small by lia; lia). exact Hr8.
Qed.
Theorem ref_open_fail_errno : ltac2:(TCodec.tc2 tcn__Js0OpenFail "SC'D'7'RAyR0%211%411&Q4y5%2214':y8%911%311p091'>&R0+1r4%3221+SoO%5231%7231'?'8&6%12E8uQ7%53421&QKr5(1%3221vR>%;3M21r6uQ6%8221&Jr7%211%B3Q441u2%>241&Q7vR5vR;vR7%44?321%J3Q<61&QJ&Q8r8%211&QH&Q;&QG(R?+:(=%33QD21%511(QF%11K%:3931%?3<1J&QI&QLr9%B11&Q:%5442Q01&RB%12R5Q8r1%32R71%QL231r:r2%211vR:%113%QK3R531p071pU<R?1'QEvR=(G&Q=vR9&R@+eXX<%22RH1&Q@%11K%756B3K1&Q9%:221&QD&QC%11QFvR8%4221%B4Q4A61p0D1p0Q21p0Q91p0QJ1p0R31p0R;1p0RB1p0RI1pR<S21pR>S81pU:S<1pT>SB1").
Proof.
intros e vals R M He HL P0 P38 P2 HR HK Habove.
pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof path_len as HPl.
destruct path_facts as (Sr & Slo & Shi & Sfit & t8 & Ht8).
pose proof (u64_range (p1 sp0 a0s path envv)) as Hpr.
rewrite <- model0_fs.
eapply (of_tail scfg sp0 (blobs0 a0s path hw rdraw) model0 Hvsp model0_halted model0_lazy model0_fd2 path (p1 sp0 a0s path envv) t8 vals);
try eassumption.
- apply path_nonul.
- rewrite P38. apply errno_ret_range. exact He.
- lia.
- lia.
- rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
- rewrite <- Ht8. apply rdn_agree. intros j Hj. apply Habove. unorm. lia.
Qed.
Lemma of_blockA : ltac2:(TCodec.tc2 tcn__Js0OpenFail "RN&QB'7'RAyR0%211%411&Q4y5%2214':y8%911%311p091'?'8&6r3%22>1uQ6%63521&QKr4(1%3221vR>%<3F21r5u2%8221&Q7vR5vR;vR7%449321%E3O61&QJ&Q8r6%211&Q;%5321>&QI&QLr7%811&Q:%5442D1&R0&RB%12Q?Ir1%32QA1%5231r8r2%211vR:%113%Q=3Q?31p071pU<QI1'QEvR=(G&Q=vR9&R@+eXX8%22R21&Q@%11L%756B3L1&Q9%:221r:%>4Q1=21p0@1p0O1p0Q61p0Q=1p0QG1p0QN1pR<R61pR>R<1pU:R@1vR<+V^m<%E2RE1%H5G31Q0B%J21A%M4Q@L1Q4p071pT:RM1").
Proof.
intros T HA.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.
pose proof (main_regs_ok sp0 a0s path envv uid hw rdraw tid regs0 mem0 Hvsp Htid ME) as HR.
pose proof (main_know_ok sp0 a0s path envv uid hw rdraw tid regs0 mem0 Hva Hve Hvsp Htid ME) as HK.
change (E0 sp0 a0s path envv hw rdraw tid regs0) with (ENV (vals0 sp0 a0s path envv tid regs0)) in HR, HK.
set (vals := vals0 sp0 a0s path envv tid regs0) in *.
assert (HL : length vals = 38%nat) by (subst vals; unfold vals0; rewrite length_app, junk_vals_length; reflexivity).
assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
assert (P2 : vals_ev vals 2 = p1 sp0 a0s path envv) by reflexivity.
clearbody vals.
pose proof model0_halted as Hh.
run_blk_keep scr0 38%nat.
apply (HA vals); try assumption.
intros x Hx. rewrite EQM. apply (mem_denot_above (ENV vals) mem0 _ 0%nat 0xe9000);
[vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia].
Qed.
Lemma openat_regs : ltac2:(TCodec.tc2 tcn__Js0OpenFail "R0'7'RAyR0%211%411&Q4y5%2214'?&QKr2u2%3221&Q7vR>vR5vR;vR7%544321%;3@71&QJ&Q8r3%211&Q;%5321?'>&Q<(R?+A(=%33I21%52:1&R@+QH%22Q11%L3Q141+:%:3Q018%<2A1&Q3%Q13Q621+;%?3Q51=%A2F1%Q53Q:1K'D&QO&RB+<%F3Q<1D%H2M1%42QB1&Q0%7221z%Q@3:21%O2<1%Q02A1%Q12G1p0Q31p0Q:1pR>QG1pU:QK1").
Proof.
intros vals R P2 HR. repeat split.
- regv HR (17 : reg). reflexivity.
- regv HR (10 : reg). apply bv_eq. reflexivity.
- regv HR (11 : reg). cbn [edenot ev ENV]. exact P2.
- regv HR (12 : reg). vm_compute. reflexivity.
Qed.
Lemma after_openat_fail : ltac2:(TCodec.tc2 tcn__Js0OpenFail "S>'D'7'RAyR0%211%411&Q4y5%2214':y8%911%311p091'>&R0+1r4%3221+SoO%5231%7231'?'8&6%12E8uQ6%53421&QKr5(1%3221vR>%;3M21r6u2%8221&Q7vR5vR;vR7%449321%D3Q661&QJ&Q8r7%211&Q;%5321>&QI&QLr8%811&Q:%5442D1&RB%12QEHr1%32QG1%Q<231r9r2%211vR:%113%Q;3QE31p071pU<QO1'QEvR=(G&Q=vR9&Q?(R?+:(=%33R621&Jr;%211%83E41&QA&R@+eXX8%22RB1+4%5221&Q@%11Q7%C5B93Q71&Q9%F221&QD&QC%11QHvR8%4221%N4Q@M61p0Q01p0Q>1p0QE1p0QL1p0R61p0R=1p0RD1pR<RM1pR>S31pU:S71pT>S=1").
Proof.
intros e vals R M He HL P0 P2 HR HK Habove.
rewrite v_addi_pc4 by lia. change (0xaa108 + 4)%Z with 0xaa10c%Z.
lazymatch type of HR with regs_ok _ ?sr ?Rc =>
pose proof (env_app_regs vals [errno_ret e] (blobs_ev (blobs0 a0s path hw rdraw)) sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
pose proof (env_app_know RSEGS vals [errno_ret e] (blobs_ev (blobs0 a0s path hw rdraw)) M knA ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2.
change (Env (vals_ev (vals ++ [errno_ret e])) (blobs_ev (blobs0 a0s path hw rdraw))) with (ENV (vals ++ [errno_ret e])) in HR2, HK2.
eapply (ref_open_fail_errno e (vals ++ [errno_ret e])); try eassumption.
- rewrite length_app, HL. reflexivity.
- rewrite vals_ev_app_l by (rewrite HL; lia). exact P0.
- rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
- rewrite vals_ev_app_l by (rewrite HL; lia). exact P2.
- apply regs_set_a0; [exact HR2|]. cbn [edenot ev ENV].
rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
Qed.
Theorem ref_open_fail_toolong : ltac2:(TCodec.tc2 tcn__Js0OpenFail "Q1'CuTP0&6'RAy8%211vR;%5221%8271'QE&QLvR=(G&Q=vR9vR<&R@yR0+V^m<%3221vR:&Q@%11<%:598431&Q9%=221&QD&QC%11FvR8%4221%F4ED61p0H1").
Proof.
intros Hlong. apply of_blockA. intros vals R M HL P0 P2 HR HK Habove.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.
destruct path_facts as (Sr & Slo & Shi & _).
pose proof (u64_range (p1 sp0 a0s path envv)) as Hpr. pose proof path_len as HPl.
destruct (openat_regs vals R P2 HR) as (A17 & A10 & A11 & A12).
assert (HF : fetch_word RSEGS (Z_to_bv 64 0xaa108) = Some ECALLW) by (vm_compute; reflexivity).
eapply (rz_openat_toolong RSEGS scfg R _ M model0 ECALLW HF is_ecall_ECALLW
model0_halted model0_lazy A17 A10 A12 (firstn 4096 path)).
- rewrite A11. rewrite <- (firstn_app_l 4096 path [Z_to_bv 8 0]) at 1 || idtac.
replace (firstn 4096 path) with (firstn 4096 (path ++ [Z_to_bv 8 0]))
by (rewrite firstn_app; replace (4096 - length path)%nat with 0%nat by lia; cbn [firstn]; apply app_nil_r).
apply (rdn_firstn RSEGS M (length path + 1)); [| lia].
rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
- intros Hin. apply path_nonul. eapply In_firstn. exact Hin.
- apply (after_openat_fail ENAMETOOLONG vals); try assumption. unfold ENAMETOOLONG. lia.
Qed.
Theorem ref_open_fail_empty : ltac2:(TCodec.tc2 tcn__Js0OpenFail "Q2'?'7'RAy8%211%411vR;(9%114%93431'QE&QLvR=(G&Q=vR9vR<&R@yR0+V^m<%3221vR:&Q@%11<%:598431&Q9%=221&QD&QC%11GvR8%4221%F4ED61p0H1").
Proof.
intros Hnil. apply of_blockA. intros vals R M HL P0 P2 HR HK Habove.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.
destruct path_facts as (Sr & Slo & Shi & _).
pose proof (u64_range (p1 sp0 a0s path envv)) as Hpr.
destruct (openat_regs vals R P2 HR) as (A17 & A10 & A11 & A12).
assert (HF : fetch_word RSEGS (Z_to_bv 64 0xaa108) = Some ECALLW) by (vm_compute; reflexivity).
eapply (rz_openat_empty RSEGS scfg R _ M model0 ECALLW HF is_ecall_ECALLW
model0_halted model0_lazy A17 A10 A12).
- split; [cbn; lia|]. split; [intros [] |]. rewrite A11.
replace (length path + 1)%nat with 1%nat in Sr by (rewrite Hnil; reflexivity).
replace (path ++ [Z_to_bv 8 0]) with [Z_to_bv 8 0] in Sr by (rewrite Hnil; reflexivity).
cbn [length Nat.add app].
rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
- apply (after_openat_fail ENOENT vals); try assumption. unfold ENOENT. lia.
Qed.
Theorem ref_open_fail_absent : ltac2:(TCodec.tc2 tcn__Js0OpenFail "QH'C&6'RAy8%211vR;%5221uSoO%8221&A'?'7%118(9%11:%533:1%711'4&Q2%11>(<%;3421':%11;&FvR8%221E(0%11@%C3631'QE&QLvR=(G&Q=vR9vR<&R@yR0+V^m<%3221vR:&Q@%11<%:598431&Q9%=221&QD&QC%11Q<%321I%E4DC51p0G1p0Q01p0Q61p0Q?1").
Proof.
intros Hlen Hne Hnd Hfsl. apply of_blockA. intros vals R M HL P0 P2 HR HK Habove.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.
destruct path_facts as (Sr & Slo & Shi & _).
pose proof (u64_range (p1 sp0 a0s path envv)) as Hpr. pose proof path_len as HPl.
destruct (openat_regs vals R P2 HR) as (A17 & A10 & A11 & A12).
assert (HF : fetch_word RSEGS (Z_to_bv 64 0xaa108) = Some ECALLW) by (vm_compute; reflexivity).
eapply (rz_openat_absent RSEGS scfg R _ M model0 ECALLW HF is_ecall_ECALLW
model0_halted model0_lazy A17 A10 A12 path).
- split; [exact Hlen|]. split; [apply path_nonul|]. rewrite A11.
rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
- exact Hne.
- exact Hnd.
- exact Hfsl.
- apply (after_openat_fail ENOENT vals); try assumption. unfold ENOENT. lia.
Qed.
Corollary ref_open_fail_toolong_w : ltac2:(TCodec.tc2 tcn__Js0OpenFail "Q4'CuTP0&6'RAy8%211vR;%5221%8271'QE&QLvR=(G&Q=vR9vR<(R?yR0+V^m<(=%43321%B14/021vR:&Q@%11?%=5<;431&Q9%@221&QD&QC%11IvR8%4221%I4HG61p0K1").
Proof.
intros H. replace (0x33bac : word) with (Z_to_bv 64 0x33bac) by (apply bv_eq; reflexivity).
apply ref_open_fail_toolong. exact H.
Qed.
Corollary ref_open_fail_empty_w : ltac2:(TCodec.tc2 tcn__Js0OpenFail "Q5'?'7'RAy8%211%411vR;(9%114%93431'QE&QLvR=(G&Q=vR9vR<(R?yR0+V^m<(=%43321%D14/021vR:&Q@%11?%=5<;431&Q9%@221&QD&QC%11JvR8%4221%I4HG61p0K1").
Proof.
intros H. replace (0x33bac : word) with (Z_to_bv 64 0x33bac) by (apply bv_eq; reflexivity).
apply ref_open_fail_empty. exact H.
Qed.
Corollary ref_open_fail_absent_w : ltac2:(TCodec.tc2 tcn__Js0OpenFail "QK'C&6'RAy8%211vR;%5221uSoO%8221&A'?'7%118(9%11:%533:1%711'4&Q2%11>(<%;3421':%11;&FvR8%221E(0%11@%C3631'QE&QLvR=(G&Q=vR9vR<(R?yR0+V^m<(=%43321%Q814/021vR:&Q@%11?%=5<;431&Q9%@221&QD&QC%11Q?%321L%H4GF51p0J1p0Q31p0Q91p0QB1").
Proof.
intros H1 H2 H3 H4. replace (0x33bac : word) with (Z_to_bv 64 0x33bac) by (apply bv_eq; reflexivity).
apply ref_open_fail_absent; assumption.
Qed.
End OpenFail.
End FPX_1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
