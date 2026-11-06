(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import RunEnv
PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg ShapeLaws Nodes
MmapSim AllocSim FileSim AgentLib SpecConsts DivergeSim SpinAlg SpinAlgX
SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibKnowFrame
Spec LibWritev RefNodes RefMemcpyLib Ju0Startup Ju0MainEntry Hoare MemSplit
Ju0OpenFail_defs Ju0OpenFail HeapIface DrvKit Ju0Drv_defs Ju0DrvLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ju0DrvA () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Fs."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Sem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.DrvKit."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0DrvA.FPX_1.DrvA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0Drv_defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0MainEntry."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RunEnv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymDrive."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymDriveX."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymRun."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1O"; "1Some"; "1bool"; "1cons"; "1list"; "1nat"; "1nil"; "1option"; "1prod"; "1true"; "2and"; "2eq"; "2not"; "3Z"; "0KA"]; ["0KF"; "4Fs"; "5mkCfg"; "6FdEntry"; "6Model"; "6VmMaps"; "6alloc_fd"; "6event"; "6fd_lookup"; "6m_fds"; "6m_fs"; "6m_vmmaps"; "7ALU_ADD"; "8alu64"; "0M"; "0RE"]; ["9blob_agree"; ":model_but_vm"; ";ENV"; ";above_sp0"; ";fds0"; ";file_k"; ";model0"; ";model1"; ";open_err_k"; "<kn_d0"; "=auxvp"; "=blobs0"; "=rnd"; "=sr_main"; "=vals0"; ">mkst"]; [">seg_rom"; "?mkModelE"; "@TSet"; "@t_alt2"; "Asrealizes"; "Bblobs_ev"; "Clog_below_b"; "DEnv"; "DKImg"; "Dkentry"; "Dsentry"; "Eknow_ok"; "Emem_denot"; "Eregs_ok"; "Fvals_ev"; "Gloaded_segments"]; ["HIn"; "Iadd"; "Ile"; "Ipow"; "0VM"; "0VM0"; "0a0s"; "0envv"; "0fs0"; "0fx"; "0hw"; "0i"; "0k"; "0log"; "0m'"; "0mem0"]; ["0path"; "0rdraw"; "0regs0"; "0scfg"; "0sp0"; "0stdin0"; "JZ_to_bv"; "Jbv"; "Jbv_unsigned"; "0tid"; "0vals"; "0x"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac lia := first [ solve [ try (match goal with H : (length _ <= S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S _)))))))))))))))))))))))))))))))))%nat |- _ => clear dependent H end); Lia.lia ] | Lia.lia ].
Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX false.
Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX true.
Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section DrvA.
Context {RE : RunEnv}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L scfg HI.
Variable sp0 : word.
Variables a0s path : list byte.
Variable envv : list (list byte).
Variable uid : word.
Variable hw : word.
Variable rdraw : EntryDraw.
Variable tid : word.
Variable regs0 : bvmap 5 word.
Variable mem0 : word -> option byte.
Variable VM0 : VmMaps.
Variable fs0 : Fs.
Variable stdin0 : InputStream.
Variable fdata : list byte.
Variable cr0 : credit.
Hypothesis Hva : valid_argv [a0s; path].
Hypothesis Hve : valid_envp envv.
Hypothesis Hvsp : valid_sp sp0.
Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
Hypothesis ME : main_entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0.
Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
Hypothesis Hpne : path <> [].
Hypothesis Hppl : openat_plain_name path = true.
Hypothesis Hfs : sc_fs scfg = true.
Hypothesis Hplen : (length path <= 4095)%nat.
Hypothesis DL : drv_layout L sp0.
Hypothesis HH0 : hi_heap HI [] cr0 mem0 VM0.
Hypothesis Hcr0 : credit_ok L cr0 65536.
Let Hsp : (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z := conj (proj1 Hvsp) (proj1 (proj2 Hvsp)).
Let Hal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).
Definition ENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev (blobs0 a0s path hw rdraw ++ [fdata])).
Definition fds0 : list (word * FdEntry) :=
[(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
(Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].
Definition model0 : Model := mkModelE fds_init VM0 stdin0 fs0 None (Some tid) None.
Definition fds1 : list (word * FdEntry) := fd_insert fds0 (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 0)).
Definition model1 (VM : VmMaps) : Model := mkModelE fds1 VM stdin0 fs0 None (Some tid) None.
Definition above_sp0 (M : word -> option byte) : Prop :=
forall a : word, (bv_unsigned sp0 <= bv_unsigned a)%Z -> M a = mem0 a.
#[using="Type"] Lemma model0_eq : ltac2:(TCodec.tc2 tcn__Ju0DrvA "H'<'D&Q6&QAvO&Q4vR5vREvR8(0'RGyR0%211%411(2vRI%2241'5y8%911%311%<11%C8BA@?>961%G3FE1").
Proof. reflexivity. Qed.
#[using="Type"] Lemma m0_fds : ltac2:(TCodec.tc2 tcn__Ju0DrvA ">'<'5'9'RGyR0%211'C%5221%711&I&Q6%211&Q4%=3521"). Proof. reflexivity. Qed.
#[using="Type"] Lemma m0_fs : ltac2:(TCodec.tc2 tcn__Ju0DrvA "7'<&A&J&Q6%211vR8%63521"). Proof. reflexivity. Qed.
#[using="Type"] Lemma m0_vm : ltac2:(TCodec.tc2 tcn__Ju0DrvA "7'<'E&K&Q6%211vR5%63521"). Proof. reflexivity. Qed.
#[using="Type"] Lemma m1_vm : ltac2:(TCodec.tc2 tcn__Ju0DrvA "9'E'<&K&Q7r1%211%411%63713pT:81"). Proof. reflexivity. Qed.
#[using="Type"] Lemma alloc_fd_fds0 : ltac2:(TCodec.tc2 tcn__Ju0DrvA ";'<'RGyR0%211&F&Q4%211&RF+3%2271%:3741"). Proof. exact (alloc_fd_init _ _ _). Qed.
#[using="Type"] Lemma fd_lookup_fds0_3 : ltac2:(TCodec.tc2 tcn__Ju0DrvA ">'<'8'C%211&H&Q4&RFyR0+3%3221%6251(0%11:%=3:31"). Proof. reflexivity. Qed.
#[using="Type"] Lemma model1_but : ltac2:(TCodec.tc2 tcn__Ju0DrvA "@'E'D&Q1&Q7r2%211r1%5221'<&K%116%811%43;81p061pTN=1pT:?1").
Proof. intros VM m' H. exact H. Qed.
#[using="a0s Hva"] Lemma path_nonul : ltac2:(TCodec.tc2 tcn__Ju0DrvA ";&=&R0'RGy8%211&RFz%2241vR@%83521%:11").
Proof.
destruct Hva as (_ & _ & _ & Hn & _). inversion Hn as [|x l Hx Hl]; subst. inversion Hl; subst. assumption.
Qed.
#[using="Type"] Lemma ENV_agree : ltac2:(TCodec.tc2 tcn__Ju0DrvA "H'5'RGyR0%211%411&Q0u4(QG&QNr1%211&QE&Q;vR6vR@vR:vRA%544321%711%<291&Q2%11<%A3@31pUFC1").
Proof. intros vals. unfold ENV. apply (blob_agree_app (vals_ev vals) (blobs0 a0s path hw rdraw) [fdata]). Qed.
#[using="uid mem0 Hvsp Htid ME"] Lemma main_regs_ok_d : ltac2:(TCodec.tc2 tcn__Ju0DrvA "=&QM&Q2&Q>vRDvR6vR@vR7vRIvRB%76654321%911&Q=%<3214").
Proof.
pose proof (main_regs_ok sp0 a0s path envv uid hw rdraw tid regs0 mem0 Hvsp Htid ME) as HR.
eapply regs_ok_bagree; [apply ENV_agree | vm_compute; reflexivity | exact HR].
Qed.
#[using="uid Hva Hve Hvsp Htid ME"] Lemma main_know_ok_d : ltac2:(TCodec.tc2 tcn__Ju0DrvA "?&QK&QO&Q2&Q>vRDvR6vR@vR7vRIvRB%76654321%911vR?&Q9%>4=321").
Proof.
pose proof (main_know_ok sp0 a0s path envv uid hw rdraw tid regs0 mem0 Hva Hve Hvsp Htid ME) as HK.
eapply know_ok_bagree; [apply ENV_agree | vm_compute; reflexivity |].
eapply ksubl_sound; [exact HK | exact kn_d0_sub].
Qed.
Definition open_err_k (KA : TSet) : Prop :=
forall e vals R M,
(1 <= e <= 4095)%Z ->
length vals = 39%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 38 = errno_ret e ->
vals_ev vals 2 = p1 sp0 a0s path envv ->
regs_ok (Env (vals_ev vals) (blobs_ev (blobs0 a0s path hw rdraw))) (sr_upd Ju0OpenFail_defs.srA (ridx 10) (EVar 38)) R ->
know_ok RSEGS (Env (vals_ev vals) (blobs_ev (blobs0 a0s path hw rdraw))) M Ju0OpenFail_defs.knA ->
above_sp0 M ->
srealizes RSEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xab160) M (seg_rom RSEGS)) model0) KA.
#[using="Type"] Lemma ENV_agree_r : ltac2:(TCodec.tc2 tcn__Ju0DrvA "H'5'RGyR0%211%411&Q0u4&Q2r1%211(QG&QN%114&QE&Q;vR6vR@vR:vRA%544321%711%;291%A3@=1pUFC1").
Proof.
intros vals. destruct (ENV_agree vals) as [A B]. split; [intros n; symmetry; apply A | intros k Hk; symmetry; apply B; exact Hk].
Qed.
#[using="uid Hva Hve Hvsp Htid ME"] Lemma main_kimg_alloc : ltac2:(TCodec.tc2 tcn__Ju0DrvA "K&QK&QO&Q2&Q>vRDvR6vR@vR7vRIvRB%76654321%911vR?(4'QI(QH+mTUH+mXP0%3221+flaA+iRo0%6221(7%119%;3:31%<3;71%J4I?>1").
Proof.
pose proof (main_know_ok sp0 a0s path envv uid hw rdraw tid regs0 mem0 Hva Hve Hvsp Htid ME) as HK.
constructor; [|constructor; [|constructor]].
- exact (know_nth RSEGS _ _ kn_main ltac:(let i := kidx kn_main (is_kimg_cov 0xe90b8 (0xea000 - 0xe90b8)) in exact i) _ HK eq_refl).
- exact (know_nth RSEGS _ _ kn_main ltac:(let i := kidx kn_main (is_kimg_cov 0xb7231 (0xc8be0 - 0xb7231)) in exact i) _ HK eq_refl).
Qed.
Definition file_k (KF : TSet) : Prop :=
forall vals R M VM (A1 : Z),
length vals = 70%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 48 = Z_to_bv 64 A1 ->
vals_ev vals 1 = p0 sp0 a0s path envv -> vals_ev vals 2 = p1 sp0 a0s path envv ->
vals_ev vals 3 = auxvp sp0 a0s path envv -> vals_ev vals 4 = rnd sp0 a0s path envv -> vals_ev vals 5 = tid ->
regs_ok (ENV vals) srC0 R -> know_ok RSEGS (ENV vals) M knC0 ->
above_sp0 M -> block_range L A1 65536 ->
hi_heap HI [(A1, 65536%Z)] (debit L cr0 65536) M VM ->
srealizes RSEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x33e70) M (seg_rom RSEGS)) (model1 VM)) KF.
#[using="uid hw rdraw Hva Hve Hvsp Hplen Hsp"] Lemma hiv_facts : ltac2:(TCodec.tc2 tcn__Ju0DrvA "QF'5'RGyR0%211%411'<&QNr1u3%3221&Q:vRDvR6vR@vR7%544321%;3=71r2u4%=221&Q<%14:987%A3C31'6&R0(4(7%114%335:1%436E1%637G1';&R2&RH%12Q0Gr5%N21C%42Q31%6241&R1&R3+2+D%3221%5271+R0%6251%?231%A2:1p0C1pTHK1p0M1p0Q41pUFQA1").
Proof.
intros vals P3 P4 i Hi.
destruct (auxvp_u sp0 a0s path envv uid hw rdraw Hva Hve Hvsp) as [A1 A2].
destruct (rnd_u sp0 a0s path envv uid hw rdraw Hva Hve Hvsp) as (R1 & R2 & _ & _).
destruct Hi as [<-|[<-|[]]]; [rewrite P3 | rewrite P4]; lia.
Qed.
#[using="Hvsp Hplen Hsp"] Lemma above_sp0_block : ltac2:(TCodec.tc2 tcn__Ju0DrvA "Q9'5'RGyR0%211%411'QJ%611'8y8%811%311p081'<&QNr3(1%3221vRD%63?21'3&QF+mXP0%23718(:%<3521&Q3%11<&QL&Q2r6%211r4r5%63321%911p091p0<1p0C1pQNK1pTLQ11pUFQ41").
Proof.
intros vals log M P0 Hb HA a Ha.
rewrite (mem_denot_above (ENV vals) M log 0%nat 0xea000 a Hb); [apply HA; exact Ha | | |];
cbn [ev ENV]; rewrite ?P0; lia.
Qed.
#[using="Type"] Lemma alu_add_w_lit : ltac2:(TCodec.tc2 tcn__Ju0DrvA "D'RGyR0%211'>'<&M(Lr2&RFr1%2291%63541&R1&RH%12=7%3216%82?1%=3?61pTJ?1pUHA1").
Proof.
intros x k. rewrite alu_add. unfold v_add. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity.
Qed.
Section SE.
Local Abbreviation SEC_T_drv_open := (ltac2:(TCodec.tc2 tcn__Ju0DrvA "Q6&QB&Q8r2%211&Q5%113r3(7'G%211%411'QD&QOvRC(B&Q?vR9vRB&RFyR0+V_`L%3221vR?&Q@%11<%:598431&Q6%=221&QCr5r4%3221%E4DC51p0G1p0M1p0Q01pQ2Q41pQ0Q51")) (only parsing).
Variable KA : ltac:(sec_ty2 constr:(SEC_T_drv_open) 0%nat 0%nat).
Variable KF : ltac:(sec_ty2 constr:(SEC_T_drv_open) 1%nat 0%nat).
Theorem drv_open : ltac:(sec_stmt2 constr:(SEC_T_drv_open) 2%nat 0%nat).
Proof using HIok uid Hva Hve Hvsp Htid ME Hfile Hpne Hppl Hfs Hplen DL HH0 Hcr0 Hsp Hal KA KF.
intros HKA HKF HKF0.
pose proof Hsp as Hsp'. pose proof Hal as Hal'.
pose proof main_regs_ok_d as HR.
assert (HK : know_ok RSEGS (ENV (vals0 sp0 a0s path envv tid regs0)) mem0 (kn_d0 ++ [KImg 0xe90b8 0xea000; KImg 0xb7231 0xc8be0]))
by (apply Forall_app; split; [apply main_know_ok_d | apply main_kimg_alloc]).
set (vals := vals0 sp0 a0s path envv tid regs0) in *.
assert (HL : length vals = 38%nat) by (subst vals; unfold vals0; rewrite length_app, junk_vals_length; reflexivity).
assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
assert (P1 : vals_ev vals 1 = p0 sp0 a0s path envv) by reflexivity.
assert (P2 : vals_ev vals 2 = p1 sp0 a0s path envv) by reflexivity.
assert (P3 : vals_ev vals 3 = auxvp sp0 a0s path envv) by reflexivity.
assert (P4 : vals_ev vals 4 = rnd sp0 a0s path envv) by reflexivity.
assert (P5 : vals_ev vals 5 = tid) by reflexivity.
destruct (main_str sp0 a0s path envv uid hw rdraw tid regs0 mem0 Hva Hve Hvsp ME 1%nat ltac:(lia)) as (Sr & Slo & Shi & Slen).
cbn [nth] in Sr, Slo, Shi, Slen.
assert (HA0 : above_sp0 mem0) by (intros a Ha; reflexivity).
clearbody vals.
run_block_keep scr0 38%nat.
assert (HH1 : hi_heap HI [] cr0 M VM0).
{ rewrite EQM. eapply (heap_block scfg L HI HIok sp0 Hsp' DL vals _ []); [exact P0 | intros i nb Hf; discriminate | vm_compute; reflexivity | exact HH0]. }
assert (HA : above_sp0 M).
{ rewrite EQM. apply above_sp0_block; [exact P0 | vm_compute; reflexivity | exact HA0]. }
assert (Sr' : rdn RSEGS M (p1 sp0 a0s path envv) (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
{ rewrite <- Sr. apply rdn_agree. intros j Hj. pose proof (u64_range (p1 sp0 a0s path envv)).
apply HA. unfold p1 in *. rewrite u_small; lia. }
clear EQM.
eapply (rz_openat_file RSEGS scfg _ _ _ model0 ECALLW); try apply is_ecall_ECALLW.
- vm_compute. reflexivity.
- reflexivity.
- reflexivity.
- regv HR (17 : reg). reflexivity.
- regv HR (10 : reg). apply bv_eq. reflexivity.
- regv HR (12 : reg). vm_compute. reflexivity.
- exact Hfs.
- rewrite m0_fds. rewrite alloc_fd_fds0. apply fd_lookup_fds0_3.
- split; [exact Hplen|]. split; [apply path_nonul|].
regv HR (11 : reg). cbn [edenot ev ENV]. rewrite P2. exact Sr'.
- exact Hpne.
- exact Hppl.
- rewrite m0_fs. exact Hfile.
-
intros e He. rewrite v_addi_pc4 by lia. change (0xab15c + 4)%Z with 0xab160%Z.
lazymatch type of HR with regs_ok _ ?sr ?Rc =>
pose proof (env_app_regs vals [errno_ret e] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
pose proof (env_app_know RSEGS vals [errno_ret e] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
change (Env (vals_ev (vals ++ [errno_ret e])) (blobs_ev (blobs0 a0s path hw rdraw ++ [fdata]))) with (ENV (vals ++ [errno_ret e])) in HR2, HK2.
eapply (HKA e (vals ++ [errno_ret e])).
+ apply openat_errnos_range. exact He.
+ rewrite length_app, HL. reflexivity.
+ rewrite vals_ev_app_l by (rewrite HL; lia). exact P0.
+ rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
+ rewrite vals_ev_app_l by (rewrite HL; lia). exact P2.
+ eapply regs_ok_bagree; [apply ENV_agree_r | vm_compute; reflexivity |].
apply regs_set_a0; [exact HR2|]. cbn [edenot ev ENV].
rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
+ eapply know_ok_bagree; [apply ENV_agree_r | vm_compute; reflexivity |].
eapply ksubl_sound; [exact HK2 | vm_compute; reflexivity].
+ exact HA.
-
rewrite v_addi_pc4 by lia. change (0xab15c + 4)%Z with 0xab160%Z.
rewrite m0_fds. rewrite alloc_fd_fds0.
change (with_fds (fd_insert fds0 (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 0))) model0) with (model1 VM0).
pose proof (regs_set_a0 (ENV vals) _ _ (Z_to_bv 64 3) (ELit 3) HR eq_refl) as HR2. clear HR. rename HR2 into HR.
run_block_keep scr0 38%nat.
cbn [mem_denot] in EQM. subst M0.
lazymatch type of HK with know_ok _ _ _ ?kn =>
eapply (malloc_site scfg L HI HIok sp0 Hsp' Hal' DL vals _ _ kn _ _ (model1 VM0) [] cr0 65536 (-128) [] [] 0x33e70 KF) end;
[ exact HR | exact HK
| rewrite HL; vm_compute; reflexivity
| rewrite HL; vm_compute; reflexivity
| rewrite HL; lia
| exact P0
| apply hiv_facts; assumption
| vm_compute; reflexivity
| regv HR (2 : reg); cbn [edenot ev ENV]; rewrite P0; apply alu_add_w_lit
| lia
| reflexivity
| regv HR (10 : reg); reflexivity
| lia
| exact Hcr0
| regv HR (4 : reg); reflexivity
| regv HR (1 : reg); reflexivity
| lia | reflexivity
| exact HH1
| reflexivity | reflexivity | reflexivity
| intros i nb Hf; discriminate
| intros v b Hf; discriminate
| exact HKF0
| ].
+
intros R' M' model' A vals' E' HL' HA' HR' HK' HH' HBUT HBR HAP HAB HBLK HIMG. subst vals' E'.
rewrite (model1_but VM0 model' HBUT).
apply (HKF (vals ++ junk_vals R') R' M' (m_vmmaps model') A); try assumption.
* rewrite HL', HL. reflexivity.
* rewrite vals_ev_app_l by (rewrite HL; lia). exact P0.
* rewrite <- HA'. rewrite HL. reflexivity.
* rewrite vals_ev_app_l by (rewrite HL; lia). exact P1.
* rewrite vals_ev_app_l by (rewrite HL; lia). exact P2.
* rewrite vals_ev_app_l by (rewrite HL; lia). exact P3.
* rewrite vals_ev_app_l by (rewrite HL; lia). exact P4.
* rewrite vals_ev_app_l by (rewrite HL; lia). exact P5.
* rewrite HL in HR'. exact HR'.
* rewrite HL in HK'. eapply ksubl_sound; [exact HK' | vm_compute; reflexivity].
* intros a Ha. rewrite (HAB a Ha). apply HA. exact Ha.
Qed.
End SE.
End DrvA.
End FPX_1.
