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
SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibKnowFrame LibTail
Spec LibWritev RefNodes RefMemcpyLib RefReadLib Ju0Startup Ju0MainEntry Hoare MemSplit
Ju0OpenFail Ju0ReadErr_defs Ju0ReadErr_tail Ju0ReadErr
HeapIface DrvKit Ju0Drv_defs Ju0DrvLib Ju0DrvA Ju0DrvG_defs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ju0DrvH () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0DrvA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0DrvH.FPX_2.DrvH."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Spec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1bool"; "1nat"; "1option"; "1true"; "2and"; "2eq"; "2not"; "3Z"; "0KA"; "4store_ok"; "5mkCfg"; "6Model"; "6VmMaps"; "6m_vmmaps"; "0M"]; ["0RE"; "7model_but_vm"; "8open_err_k"; "9model1d"; ":mkst"; ":seg_rom"; ";TSet"; ";t_alt2"; "<dot_path"; "<msg_read_error"; "<t_die"; "=srealizes"; ">loaded_segments"; "?add"; "?le"; "?lt"]; ["?of_nat"; "?pow"; "0VM"; "0VM0"; "0a"; "0a0s"; "0envv"; "0fs0"; "0fx"; "0hw"; "0i"; "0m"; "0m'"; "0mem0"; "0model0"; "0path"]; ["0rdraw"; "0regs0"; "0scfg"; "0sp0"; "0stdin0"; "@Z_to_bv"; "@bv"; "0tid"; "0x"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac lia := first [ solve [ try (match goal with H : (length _ <= S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S _)))))))))))))))))))))))))))))))))%nat |- _ => clear dependent H end); Lia.lia ] | Lia.lia ].
Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Definition STOPS_D : list Z := (0x34048 :: STOPS)%Z.
#[using="Type"] Lemma store_ok_of_defined_h : ltac2:(TCodec.tc2 tcn__Ju0DrvH "QL'QFyR0%211'3y8%511%311pSB51'8'2&Nzr2%3221&Mr3&Q0%115%4231&Q1+2+R0%3221%=251'5r1%@2?1&Or4%=11%3251%7251&7'6r7&QEr6%G21I%32Q51%511(0%11Q4%93Q431%;11p0=1pRFQ51'1&:&Lr5%?2QA1%443?1G(4%D3721p091p0Q01p0Q;1pRHQ@1pR:QB1pQ0QD1").
Proof.
intros M a m Ha Ham Hdef. destruct m as [|m']; [reflexivity|].
apply store_ok_of_all; [rewrite u_small by lia; lia|].
intros x Hx. rewrite u_small in Hx by lia. unfold wview.
specialize (Hdef (bv_unsigned x - a)%Z ltac:(lia)). replace (a + (bv_unsigned x - a))%Z with (bv_unsigned x) in Hdef by lia.
rewrite Z_to_bv_bv_unsigned in Hdef. destruct (M x); [discriminate | exfalso; apply Hdef; reflexivity].
Qed.
End FPX_1.
Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX false.
Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX true.
Tactic Notation "run_blockD_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS_D scr NX true.
Section FPX_2. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section DrvH.
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
Variable cr0 : credit.
Hypothesis Hva : valid_argv [a0s; path].
Hypothesis Hve : valid_envp envv.
Hypothesis Hvsp : valid_sp sp0.
Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
Hypothesis ME : main_entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0.
Hypothesis Hfits : entry_stack_fits sp0 [a0s; path] envv.
Hypothesis Hfs : sc_fs scfg = true.
Hypothesis Hpd : path = dot_path.
Hypothesis DL : drv_layout L sp0.
Hypothesis HH0 : hi_heap HI [] cr0 mem0 VM0.
Hypothesis Hcr0 : credit_ok L cr0 65536.
Let Hsp : (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z := conj (proj1 Hvsp) (proj1 (proj2 Hvsp)).
Let Hal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).
Let ENVd (vals : list word) : env := ENV a0s path hw rdraw [] vals.
Let model0 : Model := model0 tid VM0 fs0 stdin0.
Definition model1d (VM : VmMaps) : Model := mkModelE (fd_insert fds0 (Z_to_bv 64 3) FdDir) VM stdin0 fs0 None (Some tid) None.
#[using="Type"] Lemma m1d_but : ltac2:(TCodec.tc2 tcn__Ju0DrvH "@'='<&A&Cr2%211r1%5221'6&>%116%811%43;81p061pRJ=1pR6?1").
Proof. intros VM m' H. exact H. Qed.
Ltac norm_srget := repeat match goal with |- context [sr_get ?sr ?r] =>
let x := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with x end.
Ltac kimg_clear HK lo hi :=
lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
let H := fresh "Hki" in
pose proof (know_nth segs E M kn ltac:(let i := kidx kn (is_kimg_cov lo (hi - lo)) in exact i) _ HK eq_refl) as H;
cbn [kentry_ok] in H; intros i Hi; apply (proj2 (proj2 H)); lia
end.
Ltac kimg_clear3 HK lo m1 m2 hi :=
lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
let H1 := fresh "Hki" in let H2 := fresh "Hki" in let H3 := fresh "Hki" in
pose proof (know_nth segs E M kn ltac:(let i := kidx kn (is_kimg_cov lo (m1 - lo)) in exact i) _ HK eq_refl) as H1;
pose proof (know_nth segs E M kn ltac:(let i := kidx kn (is_kimg_cov m1 (m2 - m1)) in exact i) _ HK eq_refl) as H2;
pose proof (know_nth segs E M kn ltac:(let i := kidx kn (is_kimg_cov m2 (hi - m2)) in exact i) _ HK eq_refl) as H3;
cbn [kentry_ok] in H1, H2, H3; intros i Hi;
destruct (Z_lt_ge_dec i m1); [apply (proj2 (proj2 H1)); lia|]; destruct (Z_lt_ge_dec i m2); [apply (proj2 (proj2 H2)); lia | apply (proj2 (proj2 H3)); lia]
end.
Section SE.
Local Abbreviation SEC_T_drv_dir := (ltac2:(TCodec.tc2 tcn__Ju0DrvH "Q;&F&BvQ8vQBv@vQCvQ5vQ?vQ6vQ9vQ@vQGvQ=vQ3vQ7vQDr1%@??>=<;:987654321'K&L(;&DvQA&QEyR0+V_`L%3221&E%119%85K73A1vQ>%;221&Gr2&J&I&H%211%421H%7261%F4EQ591p0H1pDQ:1")) (only parsing).
Variable KA : ltac:(sec_ty2 constr:(SEC_T_drv_dir) 0%nat 0%nat).
Theorem drv_dir : ltac:(sec_stmt2 constr:(SEC_T_drv_dir) 1%nat 0%nat).
Proof using L HI HIok uid cr0 Hva Hve Hvsp Htid ME Hfits Hfs Hpd DL HH0 Hcr0 Hsp Hal ENVd KA.
intros HKA.
pose proof Hsp as Hsp'. pose proof Hal as Hal'.
assert (Hplen : (length path <= 4095)%nat) by (rewrite Hpd; cbn; lia).
pose proof (main_regs_ok_d sp0 a0s path envv uid hw rdraw tid regs0 mem0 [] Hvsp Htid ME) as HR.
assert (HK : know_ok RSEGS (ENV a0s path hw rdraw [] (vals0 sp0 a0s path envv tid regs0)) mem0 (kn_d0 ++ [KImg 0xe90b8 0xea000; KImg 0xb7231 0xc8be0])).
{ apply Forall_app. split; [apply (main_know_ok_d sp0 a0s path envv uid hw rdraw tid regs0 mem0 [] Hva Hve Hvsp Htid ME)
| apply (main_kimg_alloc sp0 a0s path envv uid hw rdraw tid regs0 mem0 [] Hva Hve Hvsp Htid ME)]. }
set (vals := vals0 sp0 a0s path envv tid regs0) in *.
assert (HL : length vals = 38%nat) by (subst vals; unfold vals0; rewrite length_app, junk_vals_length; reflexivity).
assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
assert (P1 : vals_ev vals 1 = p0 sp0 a0s path envv) by reflexivity.
assert (P2 : vals_ev vals 2 = p1 sp0 a0s path envv) by reflexivity.
assert (P3 : vals_ev vals 3 = auxvp sp0 a0s path envv) by reflexivity.
assert (P4 : vals_ev vals 4 = rnd sp0 a0s path envv) by reflexivity.
assert (P5 : vals_ev vals 5 = tid) by reflexivity.
destruct (path_facts sp0 a0s path envv uid hw rdraw tid regs0 mem0 Hva Hve Hvsp ME Hfits) as (Sr & Slo & Shi & Sfit & t8 & Ht8).
assert (HA0 : above_sp0 sp0 mem0 mem0) by (intros a Ha; reflexivity).
change (Env (vals_ev vals) (blobs_ev (blobs0 a0s path hw rdraw ++ [[]]))) with (ENVd vals) in HR, HK.
clearbody vals.
run_block_keep scr0 38%nat.
assert (HH1 : hi_heap HI [] cr0 M VM0).
{ rewrite EQM. eapply (heap_block scfg L HI HIok sp0 Hsp' DL vals _ []); [exact P0 | intros i nb Hf; discriminate | vm_compute; reflexivity | exact HH0]. }
assert (HA : above_sp0 sp0 mem0 M).
{ rewrite EQM. apply (above_sp0_block sp0 a0s path hw rdraw mem0 [] Hvsp Hplen vals); [exact P0 | vm_compute; reflexivity | exact HA0]. }
assert (Sr' : rdn RSEGS M (p1 sp0 a0s path envv) (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
{ rewrite <- Sr. apply rdn_agree. intros j Hj. pose proof (u64_range (p1 sp0 a0s path envv)).
apply HA. rewrite Hpd in Hj. cbn in Hj. rewrite u_small; lia. }
clear EQM.
eapply (rz_openat_dot RSEGS scfg _ _ _ model0 ECALLW); try apply is_ecall_ECALLW.
- vm_compute. reflexivity.
- reflexivity.
- reflexivity.
- regv HR (17%bv : reg). reflexivity.
- regv HR (10%bv : reg). apply bv_eq. reflexivity.
- regv HR (12%bv : reg). vm_compute. reflexivity.
- exact Hfs.
- unfold model0. rewrite m0_fds. rewrite alloc_fd_fds0. apply fd_lookup_fds0_3.
- split; [cbn; lia|]. split; [cbn; intros [E0|[]]; apply (f_equal bv_unsigned) in E0; vm_compute in E0; lia|].
regv HR (11%bv : reg). cbn [edenot ev ENVd ENV]. rewrite P2. rewrite Hpd in Sr'. exact Sr'.
-
intros e He. rewrite v_addi_pc4 by lia. change (0xab15c + 4)%Z with 0xab160%Z.
lazymatch type of HR with regs_ok _ ?sr ?Rc =>
pose proof (env_app_regs vals [errno_ret e] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
pose proof (env_app_know RSEGS vals [errno_ret e] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
change (Env (vals_ev (vals ++ [errno_ret e])) (blobs_ev (blobs0 a0s path hw rdraw ++ [[]]))) with (ENVd (vals ++ [errno_ret e])) in HR2, HK2.
eapply (HKA e (vals ++ [errno_ret e])).
+ apply openat_errnos_range. exact He.
+ rewrite length_app, HL. reflexivity.
+ rewrite vals_ev_app_l by (rewrite HL; lia). exact P0.
+ rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
+ rewrite vals_ev_app_l by (rewrite HL; lia). exact P2.
+ eapply regs_ok_bagree; [apply (ENV_agree_r a0s path hw rdraw []) | vm_compute; reflexivity |].
apply regs_set_a0; [exact HR2|]. cbn [edenot ev ENVd ENV].
rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
+ eapply know_ok_bagree; [apply (ENV_agree_r a0s path hw rdraw []) | vm_compute; reflexivity |].
eapply ksubl_sound; [exact HK2 | vm_compute; reflexivity].
+ exact HA.
-
rewrite v_addi_pc4 by lia. change (0xab15c + 4)%Z with 0xab160%Z.
unfold model0. rewrite m0_fds. rewrite alloc_fd_fds0.
change (with_fds (fd_insert fds0 (Z_to_bv 64 3) FdDir) (Ju0DrvA.model0 tid VM0 fs0 stdin0)) with (model1d VM0).
pose proof (regs_set_a0 (ENVd vals) _ _ (Z_to_bv 64 3) (ELit 3) HR eq_refl) as HR2. clear HR. rename HR2 into HR.
run_block_keep scr0 38%nat.
cbn [mem_denot] in EQM. subst M0.
lazymatch type of HK with know_ok _ _ _ ?kn =>
eapply (malloc_site scfg L HI HIok sp0 Hsp' Hal' DL vals _ _ kn _ _ (model1d VM0) [] cr0 65536 (-128) [] [] 0x33e70
(t_die (msg_read_error dot_path) fs0));
[ exact HR | exact HK
| rewrite HL; vm_compute; reflexivity
| rewrite HL; vm_compute; reflexivity
| rewrite HL; lia
| exact P0
| apply (hiv_facts sp0 a0s path envv uid hw rdraw Hva Hve Hvsp Hplen); assumption
| vm_compute; reflexivity
| regv HR (2%bv : reg); cbn [edenot ev ENVd ENV]; rewrite P0; apply alu_add_w_lit
| lia
| reflexivity
| regv HR (10%bv : reg); reflexivity
| lia
| exact Hcr0
| regv HR (4%bv : reg); reflexivity
| regv HR (1%bv : reg); reflexivity
| lia | reflexivity
| exact HH1
| reflexivity | reflexivity | reflexivity
| intros i nb Hf; discriminate
| intros v b Hf; discriminate
| apply t_emit_has_nil
| ]
end.
intros R' M' model' A vals' E' HL' HA' HR' HK' HH' HBUT HBR HAP HAB HBLK HIMG. subst vals' E'.
rewrite (m1d_but VM0 model' HBUT). rewrite (m1d_but VM0 model' HBUT) in HH'. cbn [m_vmmaps model1d mkModelE] in HH'.
set (VM1 := m_vmmaps model') in *. clearbody VM1.
set (vals1 := vals ++ junk_vals R') in *.
change (Env (vals_ev vals1) (blobs_ev (blobs0 a0s path hw rdraw ++ [[]]))) with (ENVd vals1) in HR', HK'.
rewrite HL in HL', HA', HR', HK'. change (38 + 10)%nat with 48%nat in HA'.
lazymatch type of HK' with know_ok ?segs ?E ?Mx ?kn =>
assert (HKC : know_ok segs E Mx knC0) by (eapply ksubl_sound; [exact HK' | vm_compute; reflexivity]); clear HK'; rename HKC into HK' end.
change (sr_after_call_j _ _ 38) with srC0 in HR'.
assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
assert (Q2 : vals_ev vals1 2 = p1 sp0 a0s path envv) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
assert (Q3 : vals_ev vals1 3 = auxvp sp0 a0s path envv) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P3).
assert (Q4 : vals_ev vals1 4 = rnd sp0 a0s path envv) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P4).
assert (Q5 : vals_ev vals1 5 = tid) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5).
assert (HA1 : above_sp0 sp0 mem0 M') by (intros a Ha; rewrite (HAB a Ha); apply HA; exact Ha).
pose proof (hz_of_block_range L sp0 DL _ _ HBR) as (B1 & B2 & B4).
clear HR HK HH1 HA. rename HR' into HR. rename HK' into HK.
run_block_keep scr0 70%nat.
assert (HA2 : above_sp0 sp0 mem0 M0).
{ rewrite EQM. apply (above_sp0_block sp0 a0s path hw rdraw mem0 [] Hvsp Hplen vals1); [exact Q0 | vm_compute; reflexivity | exact HA1]. }
assert (HH2 : hi_heap HI [(A, 65536%Z)] (debit L cr0 65536) M0 VM1).
{ rewrite EQM. eapply (heap_block scfg L HI HIok sp0 Hsp' DL vals1 _ []); [exact Q0 | intros i nb Hf; discriminate | vm_compute; reflexivity | exact HH']. }
destruct (hio_wf L scfg HI HIok _ _ _ _ HH2) as [WF _].
destruct (WF (A, 65536%Z) ltac:(left; reflexivity)) as (_ & HDEF & _). cbn [fst snd] in HDEF.
clear EQM.
eapply (rz_read_dir_cnt RSEGS scfg _ _ M0 (model1d VM1) ECALLW (Z_to_bv 64 3) 65536); try apply is_ecall_ECALLW.
+ vm_compute. reflexivity.
+ reflexivity.
+ reflexivity.
+ regv HR (17%bv : reg). reflexivity.
+ regv HR (10%bv : reg). reflexivity.
+ rewrite u_small by lia. lia.
+ reflexivity.
+ regv HR (12%bv : reg). reflexivity.
+ lia.
+ regv HR (11%bv : reg). cbn [edenot ev ENVd ENV]. rewrite u_small by lia. unfold TASK_SIZE. lia.
+ rewrite v_addi_pc4 by lia. change (0xab15c + 4)%Z with 0xab160%Z.
replace (errno_ret EISDIR) with (Z_to_bv 64 18446744073709551595) by (apply bv_eq; reflexivity).
pose proof (regs_set_a0 (ENVd vals1) _ _ (Z_to_bv 64 18446744073709551595) (ELit 18446744073709551595) HR eq_refl) as HR2.
clear HR. rename HR2 into HR.
run_blockD_keep scr0 70%nat.
assert (HA3 : above_sp0 sp0 mem0 M1).
{ rewrite EQM. apply (above_sp0_block sp0 a0s path hw rdraw mem0 [] Hvsp Hplen vals1); [exact Q0 | vm_compute; reflexivity | exact HA2]. }
clear EQM.
change fs0 with (m_fs (model1d VM1)).
pose proof (u64_range (p1 sp0 a0s path envv)) as Hpr.
replace (length path + 1)%nat with 2%nat in Sr by (rewrite Hpd; reflexivity).
replace (path ++ [Z_to_bv 8 0]) with [Z_to_bv 8 46; Z_to_bv 8 0] in Sr by (rewrite Hpd; reflexivity).
replace (Z.of_nat (length path)) with 1%Z in Ht8 by (rewrite Hpd; reflexivity).
unshelve (eapply (ref_read_error_dot scfg sp0 (blobs0 a0s path hw rdraw ++ [[]]) (model1d VM1) Hvsp eq_refl eq_refl eq_refl
(p1 sp0 a0s path envv) (bv_unsigned tid) _ M1 _ _ _ _ _ _ _ Htid _ _ _ _ Slo t8)).
all: lazymatch goal with
| |- getr _ _ = _ =>
rewrite (reg_val _ _ _ _ HR); norm_srget; cbn [edenot ev ENVd ENV]; rewrite ?Q0, ?Q2;
first [ reflexivity | rewrite alu_add_w_lit; f_equal; lia ]
| |- stack_writable _ _ =>
intros d m Hd Hm;
lazymatch type of HK with know_ok ?segs ?E _ ?kn =>
pose proof (kwr_store_ok segs E M1 kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608) 8388608) in exact i)
_ _ _ (-8388608 + d) m HK eq_refl ltac:(lia) ltac:(lia)) as W;
unfold adenot, v_addi in W; cbn [a_base a_off edenot ev ENVd ENV] in W; rewrite Q0 in W
end;
replace (bv_unsigned sp0 - 8388608 + d)%Z with (bv_unsigned sp0 + (-8388608 + d))%Z by lia; exact W
| |- Forall _ re_ivs =>
unfold re_ivs; repeat (apply Forall_cons; [cbn [fst snd]; unfold img_clear|]); [..|apply Forall_nil];
first [ kimg_clear HK 0x10000%Z 0xb7230%Z | kimg_clear HK 0xb7231%Z 0xb7279%Z | kimg_clear HK 0xc7279%Z 0xc8be0%Z | kimg_clear HK 0xe8cb8%Z 0xe8cd8%Z
| kimg_clear HK 0xc8c14%Z 0xc8c60%Z | kimg_clear HK 0xc8c68%Z 0xc8c80%Z | kimg_clear HK 0xc8c88%Z 0xc8ca0%Z
| kimg_clear HK 0xc8cb0%Z 0xc8cc0%Z | kimg_clear HK 0xc8cc8%Z 0xe8cb8%Z | kimg_clear3 HK 0xe8cf0%Z 0xe8cf8%Z 0xe8f18%Z 0xe8f20%Z | kimg_clear HK 0xe8f28%Z 0xe8f30%Z
| kimg_clear HK 0xe8f41%Z 0xe8f48%Z | kimg_clear HK 0xe8f50%Z 0xe8f58%Z | kimg_clear HK 0xe8f68%Z 0xe8f70%Z
| kimg_clear HK 0xe8f78%Z 0xe8fa8%Z | kimg_clear HK 0xe9460%Z 0xea000%Z ]
| |- cell _ 0xc8c08 4 _ =>
unfold cell; krd HK 0xc8c08%Z 4%nat Htc; rewrite Htc; cbn [ev ENVd ENV]; rewrite Q5;
rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia);
rewrite Z_to_bv_bv_unsigned; reflexivity
| |- cell _ _ _ _ => unfold cell; krd_solve HK
| |- forall i, _ -> ?Mx _ = Some _ =>
lazymatch type of HK with know_ok ?segs ?E _ ?kn =>
pose proof (know_nth segs E Mx kn ltac:(let i := kidx kn (kentry_eqb (KBlob (SA (ELit 0) 0xe8f20) (ELit 8) 2)) in exact i)
_ HK eq_refl) as KB;
cbn [kentry_ok] in KB; destruct KB as (_ & _ & KB); unfold estart, elenZ in KB;
cbn [a_base a_off edenot eb ENVd ENV] in KB; rewrite ?(u_small 8), ?(u_small 0) in KB by lia;
intros i Hi; replace (954144 + i)%Z with (0 + 954144 + i)%Z by lia; apply KB; lia
end
| |- length _ = 8%nat => cbn; reflexivity
| |- rdn _ _ _ 2 = _ =>
rewrite <- Sr; apply rdn_agree; intros j Hj; apply HA3; rewrite !u_small by lia; lia
| |- rdn _ _ _ 8 = _ =>
rewrite <- Ht8; apply rdn_agree; intros j Hj; apply HA3; rewrite (u_small (bv_unsigned (p1 sp0 a0s path envv) + 1)) by lia;
rewrite u_small by lia; lia
| |- _ => lia
end.
Qed.
End SE.
End DrvH.
End FPX_2.
