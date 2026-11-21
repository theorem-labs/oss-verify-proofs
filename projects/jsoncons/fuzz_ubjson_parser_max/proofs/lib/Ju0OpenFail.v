(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: decoded 13 encoded statements, re-parameterised main_entry and p1 over launch input inp and entry, added init_reserved to model0, and reworked path_facts via main_entry_inp with new TASK_SIZE bound subgoals in open-fail proofs; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/Ub0OpenFail.v, 80 lines within its lines 32-316. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import RunEnv
PropExec CatExec CatSim SeqExec StoreOk ShapeAlg DivergeSim SpinAlg SpinAlgX Nodes Hoare Frame
MmapSim AllocSim FileSim AgentLib ArgvEnv MuslStrlen RefLayout
SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4
Spec LibWritev RefNodes Ju0ExitBase Ju0Exit RefMemcpyLib Ju0MemcpyBase Ju0Memcpy Ju0Memchr Ju0Strnlen
Ju0Startup Ju0StartupFacts Ju0MainEntry LibTail.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import Ju0OpenFail_defs Ju0OpenFail_tail Ju0OpenFail_tail2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ju0OpenFail () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Fs."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0MainEntry."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0OpenFail.FPX_1.OpenFail."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0OpenFail_defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Spec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymRun."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1O"; "1Some"; "1app"; "1bool"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1prod"; "1true"; "2I"; "2and"; "2eq"]; ["2ex"; "2not"; "3add"; "4le"; "5Z"; "6Fs"; "6fs_lookup"; "7mkCfg"; "8FdChannel"; "8FdEntry"; "8errno_ret"; "8fd_lookup"; "8m_fds"; "8m_fs"; "8m_halted"; "8m_vm_lazy"]; ["9open_ignored_flags"; "9openat_errnos"; "9openat_plain_name"; ":AT_FDCWD"; ";bvmap"; "0M"; "0R"; "<p1"; "=ENV"; "=model0"; ">knA"; ">srA"; "?getr"; "?mkst"; "?rdn"; "?regupd"]; ["?seg_rom"; "?v_addi"; "@TSet"; "Amsg_cannot_open"; "At_die"; "Bsrealizes"; "CEVar"; "Cridx"; "Csr_upd"; "Dknow_ok"; "Dregs_ok"; "Evals_ev"; "Floaded_segments"; "GIn"; "Hadd"; "Hldiff"]; ["Hle"; "Hof_nat"; "Hpow"; "Hsub"; "0T"; "0a0s"; "0e"; "0envv"; "0fs0"; "0fx"; "0mem0"; "0path"; "0regs0"; "0scfg"; "0sp0"; "IBV"]; ["IZ_to_bv"; "Ibv"; "Ibv_unsigned"; "0t8"; "0vals"; "0x"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Lemma errno_ret_range : forall e, (1 <= e <= 4095)%Z ->
(2 ^ 64 - 4095 <= bv_unsigned (errno_ret e))%Z.
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
Lemma openat_errnos_range : forall e, In e openat_errnos -> (1 <= e <= 4095)%Z.
Proof.
intros e He. unfold openat_errnos in He. cbn in He.
unfold ENOMEM, EACCES, EMFILE, ENFILE in He. lia.
Qed.
Section OpenFail.
Context {RE : RunEnv}. Context {RO : ReaderOn}.
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
Variable inp : ProcInput.
Variable entry : word.
Hypothesis ME : main_entry inp mbase entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0.
Hypothesis Hfs : sc_fs scfg = true.
Definition ENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev (blobs0 a0s path hw rdraw)).
Definition model0 : Model :=
mkModelE fds_init (mkVmMapsFull (init_reserved (segments_reserved RSEGS) mbase sp0 (in_kernel inp)) [] [] brk brk lim mbase sp0) stdin0 fs0 None (Some tid) None.
Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
Lemma model0_halted : m_halted model0 = None.
Proof. reflexivity. Qed.
Lemma model0_lazy : m_vm_lazy model0 = [].
Proof. reflexivity. Qed.
Lemma model0_fd2 : fd_lookup (m_fds model0) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
Proof. reflexivity. Qed.
Lemma model0_fs : m_fs model0 = fs0.
Proof. reflexivity. Qed.
Lemma path_nonul : ~ In (Z_to_bv 8 0) path.
Proof.
destruct Hva as (_ & _ & _ & Hn & _). inversion Hn as [|x l Hx Hl]; subst. inversion Hl; subst. assumption.
Qed.
Lemma path_len : (Z.of_nat (length path) <= 131071)%Z.
Proof.
destruct Hva as (_ & _ & Hl & _ & _). inversion Hl as [|x l Hx Hl']; subst. inversion Hl'; subst. assumption.
Qed.
Lemma path_facts :
rdn RSEGS mem0 (p1 a0s path envv rdraw inp) (length path + 1) = Some (path ++ [Z_to_bv 8 0])
/\ (bv_unsigned sp0 <= bv_unsigned (p1 a0s path envv rdraw inp))%Z
/\ (bv_unsigned (p1 a0s path envv rdraw inp) <= bv_unsigned sp0 + 2107576)%Z
/\ (bv_unsigned (p1 a0s path envv rdraw inp) + Z.of_nat (length path) + 9 <= 0x800000000000)%Z
/\ exists t8, rdn RSEGS mem0 (Z_to_bv 64 (bv_unsigned (p1 a0s path envv rdraw inp) + Z.of_nat (length path))) 8 = Some t8.
Proof.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.
destruct (main_str sp0 a0s path envv uid hw rdraw tid regs0 mem0 Hva Hve Hvsp Htid inp mbase entry ME 1%nat ltac:(lia)) as (Sr & Slo & Shi & Slen).
pose proof (main_str_fits sp0 a0s path envv uid hw rdraw tid regs0 mem0 Hva Hve Hvsp Htid inp mbase entry ME 1%nat ltac:(lia)) as Sfit.
cbn [nth] in Sr, Slo, Shi, Slen, Sfit. unfold p1.
split; [exact Sr|]. split; [exact Slo|]. split; [exact Shi|]. split; [exact Sfit|].
destruct (main_entry_inp inp mbase entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0 ME) as (Eav & Eev & _ & _ & Hvl & brk' & Hlau).
pose proof (entry_stack_image_no_wrap Sv48 inp mbase RPH entry sp0 brk' rdraw Hlau) as Hnw.
destruct (read_word_stack Sv48 RSEGS inp mbase RPH entry sp0 brk' rdraw 1 (length path) Hlau ltac:(rewrite Eav; cbn; lia) ltac:(rewrite Eav; cbn; lia) Hnw)
as (t8 & Hl8 & Hr8).
exists t8. rewrite w_add_nat in Hr8. rewrite Eav, Eev in Hr8.
pose proof (u64_range (cat_argv_ptr (ed_top rdraw) [a0s; path] envv (in_execfn inp) 1)).
rewrite (main_entry_rdn_above inp mbase entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0 ME) by (rewrite u_small by lia; lia).
pose proof (rdn_wmem_stack RSEGS inp mbase RPH entry sp0 rdraw) as Hw. unfold wmem in Hw.
rewrite Hw by (rewrite u_small by lia; lia). exact Hr8.
Qed.
Theorem ref_open_fail_errno : forall e vals R M,
(1 <= e <= 4095)%Z ->
length vals = 39%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 38 = errno_ret e ->
vals_ev vals 2 = p1 a0s path envv rdraw inp ->
regs_ok (ENV vals) (sr_upd srA (ridx 10) (EVar 38)) R -> know_ok RSEGS (ENV vals) M knA ->
(forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x) ->
srealizes RSEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xab160) M (seg_rom RSEGS)) model0)
(t_die (msg_cannot_open path) fs0).
Proof.
intros e vals R M He HL P0 P38 P2 HR HK Habove.
pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof path_len as HPl.
destruct path_facts as (Sr & Slo & Shi & Sfit & t8 & Ht8).
pose proof (u64_range (p1 a0s path envv rdraw inp)) as Hpr.
rewrite <- model0_fs.
eapply (of_tail scfg sp0 (blobs0 a0s path hw rdraw) model0 Hvsp model0_halted model0_lazy model0_fd2 ltac:(rdr) path (p1 a0s path envv rdraw inp) t8 vals);
try eassumption.
- apply path_nonul.
- rewrite P38. apply errno_ret_range. exact He.
- lia.
- lia.
- rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
- rewrite <- Ht8. apply rdn_agree. intros j Hj. apply Habove. unorm. lia.
Qed.
Lemma of_blockA : forall T,
(forall vals R M,
length vals = 38%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 a0s path envv rdraw inp ->
regs_ok (ENV vals) srA R -> know_ok RSEGS (ENV vals) M knA ->
(forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x) ->
srealizes RSEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xab15c) M (seg_rom RSEGS)) model0) T) ->
srealizes RSEGS scfg (mkCfg (mkst regs0 (Z_to_bv 64 0x33e1c) mem0 (seg_rom RSEGS)) model0) T.
Proof.
intros T HA.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.
pose proof (main_regs_ok sp0 a0s path envv uid hw rdraw tid regs0 mem0 Hva Hve Hvsp Htid inp mbase entry ME) as HR.
pose proof (main_know_ok sp0 a0s path envv uid hw rdraw tid regs0 mem0 Hva Hve Hvsp Htid inp mbase entry ME) as HK.
change (E0 sp0 a0s path envv hw rdraw tid regs0 inp) with (ENV (vals0 sp0 a0s path envv rdraw tid regs0 inp)) in HR, HK.
set (vals := vals0 sp0 a0s path envv rdraw tid regs0 inp) in *.
assert (HL : length vals = 38%nat) by (subst vals; unfold vals0; rewrite length_app, junk_vals_length; reflexivity).
assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
assert (P2 : vals_ev vals 2 = p1 a0s path envv rdraw inp) by reflexivity.
clearbody vals.
pose proof model0_halted as Hh.
run_blk_keep scr0 38%nat.
apply (HA vals); try assumption.
intros x Hx. rewrite EQM. apply (mem_denot_above (ENV vals) mem0 _ 0%nat 0xea000);
[vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia].
Qed.
Lemma openat_regs : forall vals R,
vals_ev vals 2 = p1 a0s path envv rdraw inp -> regs_ok (ENV vals) srA R ->
getr R 17 = Z_to_bv 64 56 /\ getr R 10 = AT_FDCWD /\ getr R 11 = p1 a0s path envv rdraw inp
/\ Z.ldiff (bv_unsigned (getr R 12)) open_ignored_flags = 0%Z.
Proof.
intros vals R P2 HR. repeat split.
- regv HR (17 : reg). reflexivity.
- regv HR (10 : reg). apply bv_eq. reflexivity.
- regv HR (11 : reg). cbn [edenot ev ENV]. exact P2.
- regv HR (12 : reg). vm_compute. reflexivity.
Qed.
Lemma after_openat_fail : forall e vals R M,
(1 <= e <= 4095)%Z ->
length vals = 38%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 a0s path envv rdraw inp ->
regs_ok (ENV vals) srA R -> know_ok RSEGS (ENV vals) M knA ->
(forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x) ->
srealizes RSEGS scfg (mkCfg (mkst (regupd R 10 (errno_ret e)) (v_addi (Z_to_bv 64 0xab15c) 4) M (seg_rom RSEGS)) model0)
(t_die (msg_cannot_open path) fs0).
Proof.
intros e vals R M He HL P0 P2 HR HK Habove.
rewrite v_addi_pc4 by lia. change (0xab15c + 4)%Z with 0xab160%Z.
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
Theorem ref_open_fail_toolong : ltac2:(TCodec.tc2 tcn__Ju0OpenFail "Q1'CuTP0&6'RAy8%211vR;%5221%8271'QE&QLvR=(G&Q=vR9vR<&R@yR0+V_`L%3221vR:&Q@%11<%:598431&Q9%=221&QD&QC%11FvR8%4221%F4ED61p0H1").
Proof.
intros Hlong. apply of_blockA. intros vals R M HL P0 P2 HR HK Habove.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.
destruct path_facts as (Sr & Slo & Shi & Sfit & _).
pose proof (u64_range (p1 a0s path envv rdraw inp)) as Hpr. pose proof path_len as HPl.
destruct (openat_regs vals R P2 HR) as (A17 & A10 & A11 & A12).
assert (HF : fetch_word RSEGS (Z_to_bv 64 0xab15c) = Some ECALLW) by (vm_compute; reflexivity).
eapply (rz_openat_toolong RSEGS scfg R _ M model0 ECALLW HF is_ecall_ECALLW
model0_halted model0_lazy A17 A10 A12 (firstn 4096 path)).
- rewrite A11. rewrite <- (firstn_app_l 4096 path [Z_to_bv 8 0]) at 1 || idtac.
replace (firstn 4096 path) with (firstn 4096 (path ++ [Z_to_bv 8 0]))
by (rewrite firstn_app; replace (4096 - length path)%nat with 0%nat by lia; cbn [firstn]; apply app_nil_r).
apply (rdn_firstn RSEGS M (length path + 1)); [| lia].
rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
- intros Hin. apply path_nonul. eapply In_firstn. exact Hin.
- rewrite A11. unfold TASK_SIZE. lia.
- apply (after_openat_fail ENAMETOOLONG vals); try assumption. unfold ENAMETOOLONG. lia.
Qed.
Theorem ref_open_fail_empty : ltac2:(TCodec.tc2 tcn__Ju0OpenFail "Q2'?'7'RAy8%211%411vR;(9%114%93431'QE&QLvR=(G&Q=vR9vR<&R@yR0+V_`L%3221vR:&Q@%11<%:598431&Q9%=221&QD&QC%11GvR8%4221%F4ED61p0H1").
Proof.
intros Hnil. apply of_blockA. intros vals R M HL P0 P2 HR HK Habove.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.
destruct path_facts as (Sr & Slo & Shi & Sfit & _).
pose proof (u64_range (p1 a0s path envv rdraw inp)) as Hpr.
destruct (openat_regs vals R P2 HR) as (A17 & A10 & A11 & A12).
assert (HF : fetch_word RSEGS (Z_to_bv 64 0xab15c) = Some ECALLW) by (vm_compute; reflexivity).
eapply (rz_openat_empty RSEGS scfg R _ M model0 ECALLW HF is_ecall_ECALLW
model0_halted model0_lazy A17 A10 A12).
- split; [cbn; lia|]. split; [intros [] |].
split; [rewrite A11; cbn [length]; unfold TASK_SIZE; lia|]. rewrite A11.
replace (length path + 1)%nat with 1%nat in Sr by (rewrite Hnil; reflexivity).
replace (path ++ [Z_to_bv 8 0]) with [Z_to_bv 8 0] in Sr by (rewrite Hnil; reflexivity).
cbn [length Nat.add app].
rewrite <- Sr; apply rdn_agree; intros j Hj; apply Habove; rewrite u_small by lia; lia.
- apply (after_openat_fail ENOENT vals); try assumption. unfold ENOENT. lia.
Qed.
Theorem ref_open_fail_absent : ltac2:(TCodec.tc2 tcn__Ju0OpenFail "QH'C&6'RAy8%211vR;%5221uSoO%8221&A'?'7%118(9%11:%533:1%711'4&Q2%11>(<%;3421':%11;&FvR8%221E(0%11@%C3631'QE&QLvR=(G&Q=vR9vR<&R@yR0+V_`L%3221vR:&Q@%11<%:598431&Q9%=221&QD&QC%11Q<%321I%E4DC51p0G1p0Q01p0Q61p0Q?1").
Proof.
intros Hlen Hne Hnd Hfsl. apply of_blockA. intros vals R M HL P0 P2 HR HK Habove.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.
destruct path_facts as (Sr & Slo & Shi & Sfit & _).
pose proof (u64_range (p1 a0s path envv rdraw inp)) as Hpr. pose proof path_len as HPl.
destruct (openat_regs vals R P2 HR) as (A17 & A10 & A11 & A12).
assert (HF : fetch_word RSEGS (Z_to_bv 64 0xab15c) = Some ECALLW) by (vm_compute; reflexivity).
eapply (rz_openat_absent RSEGS scfg R _ M model0 ECALLW HF is_ecall_ECALLW
model0_halted model0_lazy A17 A10 A12 path).
- split; [exact Hlen|]. split; [apply path_nonul|]. rewrite A11.
split; [unfold TASK_SIZE; lia|].
rewrite <- Sr; apply rdn_agree; intros j Hj; apply Habove; rewrite u_small by lia; lia.
- exact Hne.
- exact Hnd.
- exact Hfsl.
- apply (after_openat_fail ENOENT vals); try assumption. unfold ENOENT. lia.
Qed.
Corollary ref_open_fail_toolong_w : ltac2:(TCodec.tc2 tcn__Ju0OpenFail "Q4'CuTP0&6'RAy8%211vR;%5221%8271'QE&QLvR=(G&Q=vR9vR<(R?yR0+V_`L(=%43321%B14/021vR:&Q@%11?%=5<;431&Q9%@221&QD&QC%11IvR8%4221%I4HG61p0K1").
Proof.
intros H. replace (0x33e1c : word) with (Z_to_bv 64 0x33e1c) by (apply bv_eq; reflexivity).
apply ref_open_fail_toolong. exact H.
Qed.
Corollary ref_open_fail_empty_w : ltac2:(TCodec.tc2 tcn__Ju0OpenFail "Q5'?'7'RAy8%211%411vR;(9%114%93431'QE&QLvR=(G&Q=vR9vR<(R?yR0+V_`L(=%43321%D14/021vR:&Q@%11?%=5<;431&Q9%@221&QD&QC%11JvR8%4221%I4HG61p0K1").
Proof.
intros H. replace (0x33e1c : word) with (Z_to_bv 64 0x33e1c) by (apply bv_eq; reflexivity).
apply ref_open_fail_empty. exact H.
Qed.
Corollary ref_open_fail_absent_w : ltac2:(TCodec.tc2 tcn__Ju0OpenFail "QK'C&6'RAy8%211vR;%5221uSoO%8221&A'?'7%118(9%11:%533:1%711'4&Q2%11>(<%;3421':%11;&FvR8%221E(0%11@%C3631'QE&QLvR=(G&Q=vR9vR<(R?yR0+V_`L(=%43321%Q814/021vR:&Q@%11?%=5<;431&Q9%@221&QD&QC%11Q?%321L%H4GF51p0J1p0Q31p0Q91p0QB1").
Proof.
intros H1 H2 H3 H4. replace (0x33e1c : word) with (Z_to_bv 64 0x33e1c) by (apply bv_eq; reflexivity).
apply ref_open_fail_absent; assumption.
Qed.
End OpenFail.
End FPX_1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
