(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "iff"; "not"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "eval"; "holds"; "SLit"; "ss_facts"; "SVar"; "rw"; "sv"; "SLBytes"; "SAlu"; "SPBranch"; "SExt"; "agree_below"; "sprop_below"; "SPNot"; "rl"; "ss_next"; "reg_sv"; "ss_lenient"; "sstate"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init"; "segsU"; "S0_U"; "c0U"; "imgU"; "pcU"; "phU"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Start.Start"; "G"; "QE_ecall"; "Q_ecall"; "@Corelib.Init.Datatypes"; "list"; "cons"; "app"; "bool"; "true"; "false"; "nil"; "length"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "modulo"; "pow"; "mul"; "of_nat"; "land"; "@Corelib.Lists.ListDef"; "Forall"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "ok_frame"; "LQ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "triple1"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.StartStates"; "F_pn"; "F_env"; "E_ecall"; "S0_U_lit"; "GSTART"; "E_env0"; "E_env1"; "E_pn_other"; "E_pn_slash"; "S_tid"; "s_env0"; "s_pn_other"; "s_pn_slash"; "C_env0"; "C_pn0"; "F_tid"; "S_aux"; "S_main"; "cuts_start"; "var_envx"; "var_pn"; "var_pnx"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "with_tid"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "wsub_get"; "wsub_id_below"; "wsub"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_NE"; "BC_EQ"; "ALU_AND"; "ALU_SLL"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Start"; "K0"; "K1"; "Posts_start"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "ok_pframe"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "RsCut"; "mkLeaf"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "cfg_model"; "mkEntry"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Fork"; "PID_MAX_ENVELOPE"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout"; "env_bytes"; "valid_entry48"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState"; "Jinit"; "@Stdlib.PArith.BinPos.Pos"; "lt"].
#[local] Ltac2 tb__ s := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Kernel.Fork.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall Glue3.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CfgGlue InitLayout InitState StartGlue.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init StartStates.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition K0 (m0 : Model) (tr : list event) (md : Model) : Prop := ltac2:(tb__ "0|0|
S1S0S28S56A1Vtr;S2eS56A1A3S0S57Vmd;Vm0;A3A2").
Definition K1 (m0 : Model) (tr : list event) (md : Model) : Prop := ltac2:(tb__ "0|3|
S1S0S28S56A1Vtr;S2eS56A1A3S2S23Q40M0A1M1G1S1S1S32Z0S22G0R1A2M2A2S32G2S6dA2A2S0S57Vmd;S58R1Vm0;A2A3A2Ltid;A2A2").

Definition Posts_start : list leaf := ltac2:(tb__ "0|0|
S29S68S6aS51S69A2S2eS68A1A3").

Section Start.
Variable sp brk mb : word.
Variable draw : EntryDraw.
Variable lim : Z.
Variable inp : ProcInput.
Hypothesis Hent : ltac2:(tb__ "0|0|
S6fS1fS6cVsp;Vbrk;Vmb;Vdraw;A4Vinp;A3").
Hypothesis Hinp : valid_input_either inp.
Variable rhoI : valuation.
Hypothesis HJ : ltac2:(tb__ "0|0|
S70S1cS20S21Vsp;Vdraw;Vinp;VrhoI;A7").

Let argv := in_argv inp.
Let envp := in_envp inp.
Let argv0 := nth 0 argv [].
Let ENVC := Z.of_nat (length envp).
Let m0 : Model := ltac2:(tb__ "0|0|
S6bS1eVsp;Vbrk;Vmb;Vdraw;Vlim;Vinp;A6A1").

Lemma m0_tid : m_tid m0 = None.
Proof using brk inp lim mb sp. reflexivity. Qed.
Lemma m0_idle : model_idle m0.
Proof using brk inp lim mb sp. split; reflexivity. Qed.

Definition G (rho : valuation) : Prop := agree_below 20 rhoI rho.

Lemma G_stable : ltac2:(tb__ "0|0|
S6S6S25R2A1S12S44R3R2A3S25R3A1F_;F_;Fr2;Fr1;").
Proof using . intros r1 r2 H1 H2. unfold G in *. eapply agree_below_trans; eauto. Qed.
Lemma G_stable20 : ltac2:(tb__ "0|0|
S6S6S25R2A1S12P14R3R2A3S25R3A1F_;F_;Fr2;Fr1;").
Proof using . exact G_stable. Qed.
Lemma G_rhoI : G rhoI.
Proof using . apply agree_below_refl. Qed.

Lemma valid_sp_sp : valid_sp sp.
Proof using Hent. exact (proj1 Hent). Qed.
Lemma valid_argv_argv : valid_argv argv.
Proof using Hinp. exact (proj1 Hinp). Qed.
Lemma valid_envp_envp : valid_envp envp.
Proof using Hinp. exact (proj1 (proj2 Hinp)). Qed.

Lemma G_rl1 : ltac2:(tb__ "0|0|
S6S25R1A1S0S28S23Q8A1A1S15R2P1A2S6eVsp;Vargv;Venvp;A3A3F_;Frho;").
Proof using HJ. intros rho (_ & Hl & _). rewrite <- Hl. apply (ji_env _ _ _ _ _ _ _ HJ). Qed.
Lemma G_rl2 : ltac2:(tb__ "0|2|
S6S25R1A1S0S28S23Q8M0A1M1A1S15R2P2A2S2aG1Vargv0;S29G1S24G0Z0A2S2eG1A1A3A3A3F_;Frho;").
Proof using HJ argv. intros rho (_ & Hl & _). rewrite <- Hl. apply (ji_str0 _ _ _ _ _ _ _ HJ). Qed.
Lemma G_rw3 : ltac2:(tb__ "0|0|
S6S25R1A1S0S1aS22Q40ScR2P3A2A2VENVC;A3F_;Frho;").
Proof using HJ Hinp envp.
  intros rho (Hw & _ & _). rewrite <- Hw by (cbv; reflexivity). rewrite (ji_envc _ _ _ _ _ _ _ HJ).
  pose proof (proj1 valid_envp_envp). apply Z_to_bv_small. rewrite mod64. subst ENVC envp. lia.
Qed.
Lemma G_rw5 : ltac2:(tb__ "0|0|
S6S25R1A1S0S1aS22Q40ScR2P5A2A2S36S2fS23Q8A1Vargv0;A2A1A3F_;Frho;").
Proof using ENVC HJ Hinp argv.
  intros rho (Hw & _ & _). rewrite <- Hw by (cbv; reflexivity). rewrite (ji_len0 _ _ _ _ _ _ _ HJ).
  pose proof valid_argv_argv as (H1 & _ & H3 & _).
  apply Z_to_bv_small. rewrite mod64. subst argv0 argv.
  destruct (in_argv inp) as [|a r]; [cbn; lia|]. cbn. inversion H3. lia.
Qed.
Lemma ENVC_bound : 0 <= ENVC <= 256.
Proof using Hinp envp. pose proof (proj1 valid_envp_envp). subst ENVC envp. lia. Qed.
Lemma len0_bound : Z.of_nat (length argv0) <= 131071.
Proof using ENVC Hinp argv.
  pose proof valid_argv_argv as (H1 & _ & H3 & _). subst argv0 argv.
  destruct (in_argv inp) as [|a r]; [cbn in H1; lia|]. cbn. inversion H3. lia.
Qed.

Lemma sll3_val : ltac2:(tb__ "0|0|
S6S25R1A1S0S1aS22Q40S7R2SfS61SbP3A1S9Z3A1A3A2A2S35Z8VENVC;A2A3F_;Frho;").
Proof using HJ Hinp envp.
  intros rho Hg. cbn [eval]. rewrite sll_val. change (3 mod 64) with 3.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. rewrite (G_rw3 rho Hg).
  pose proof ENVC_bound. rewrite Z.mod_small; [lia|]. rewrite pow64. lia.
Qed.

Lemma land7 : ltac2:(tb__ "0|0|
S1aS30Z0R1A2S0S1aS37R2Z7A2S33R2Z8A2A3F_;Fz;").
Proof using ENVC. intros z Hz. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma and7_val : ltac2:(tb__ "0|1|
S6SdS0S1aS22Q40M0S7R2SfS60R1S9Z7A1A3A2A2S33S22G0S7R2R1A2A2Z8A2A3Fe;Frho;").
Proof using ENVC.
  intros rho e. cbn [eval]. unfold alu64, alu. rewrite bv_and_unsigned, Z_to_bv_unsigned.
  change (bv_wrap 64 7) with 7. apply land7. apply (proj1 (urange _)).
Qed.

Lemma add_lit_small : ltac2:(tb__ "0|1|
S6SdS1aS1aS0S1aS22Q40M0S7R4R3A2A2R1A3S30Z0R3A2S32S31R3R4A2S34Z2Z40A2A2S0S1aS22G0S7R7SfS5dR6S9R5A1A3A2A2S31R4R5A2A3F_;F_;F_;Fx;Fc;Fe;Frho;").
Proof using ENVC.
  intros rho e c x Hx Hc Hb. cbn [eval]. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned, Hx.
  unfold bv_wrap. rewrite mod64. pose proof (urange (eval rho e)). rewrite (Z.mod_small c) by lia.
  apply Z.mod_small. lia.
Qed.

Lemma env_load : ltac2:(tb__ "0|5|
S6S25R1A1S1aS0S1aS22Q40M0ScR3P14M1A2A2R1A3S1S30Z0M2R2A2S30R2S35Z8M3VENVC;A2M4A2A2S0S1aS33R3G3A2G2A3S3S0S1aS22G0S7R6SeP1SbG1A1G3A3A2A2G2A3S0S1aR4G4A3A2F_;F_;F_;Fo;F_;Frho;").
Proof using HJ Hent Hinp argv envp.
  intros rho Hg o Ho Hr Hm. cbn [eval]. rewrite (G_rl1 rho Hg), Ho.
  apply (env_word sp argv envp valid_sp_sp valid_argv_argv valid_envp_envp o Hr Hm).
Qed.

Lemma pn_load : ltac2:(tb__ "0|5|
S6S25R1A1S1aS0S1aS22Q40M0ScR3P15M1A2A2R1A3S1S30Z0M2R2A2S30R2S36S2fS23Q8M3A1Vargv0;A2A1M4A2A2S3S0S1aS22G0S7R5S11S2dG3SeP2SbG1A1Z1A3A3A2A2G2A3S0S1aR3G4A3A2F_;F_;Fi;F_;Frho;").
Proof using ENVC HJ Hinp argv.
  intros rho Hg i Hi Hr. cbn [eval]. rewrite (G_rl2 rho Hg), Hi.
  replace i with (Z.of_nat (Z.to_nat i)) by lia.
  rewrite sublist_byte by (rewrite length_app; cbn; lia). rewrite byte_val.
  pose proof (str0_byte argv valid_argv_argv (Z.to_nat i) ltac:(subst argv0; lia)) as HB. subst argv0. rewrite HB. lia.
Qed.

Ltac fwd H := match type of H with Forall _ (_ :: _) => apply Forall_cons_iff in H; destruct H as [? H] end.

Lemma env_leaf_facts : ltac2:(tb__ "0|4|
S6S28S5A1S5S25R3A1S38S5S8R4A1S29S5R2S2aS5S41R3A3A3A3S1S8R5R3A2S1S1S30Z0M0S22Q40ScR5P14A2A2M1A2S30G1S35Z8M2VENVC;A2M3A2A2S1S0S1aS33G1G2A2G0A3S30G3Z800A2A2A2A2F_;F_;Ff0;Ffs;Frho;").
Proof using HJ Hinp envp.
  intros rho fs f0 Hg HF. pose proof ENVC_bound.
  apply Forall_cons_iff in HF as [H0 HF]. unfold F_env in HF. cbn [app] in HF.
  apply Forall_cons_iff in HF as [H1 HF]. apply Forall_cons_iff in HF as [H2 HF]. apply Forall_cons_iff in HF as [H3 _].
  cbn [holds] in H1, H2, H3. rewrite (sll3_val rho Hg) in H1. change (eval rho (SVar 20)) with (rw rho 20) in H1, H2.
  apply (f_equal bv_unsigned) in H3. rewrite and7_val in H3. change (eval rho (SVar 20)) with (rw rho 20) in H3.
  cbn [eval] in H2, H3. rewrite !Z_to_bv_unsigned in H2, H3. change (bv_wrap 64 0) with 0 in H3. change (bv_wrap 64 2048) with 2048 in H2.
  pose proof (urange (rw rho 20)). repeat split; auto; lia.
Qed.

Lemma E_env0_facts : ltac2:(tb__ "0|0|
S0S28S5A1SaS45A1S29S5S10S5eSeP1SbP14A1Z8A3S9Z0A1A3S2aS5S41SaS43A1A3A3A3").
Proof using . reflexivity. Qed.
Lemma E_env1_facts : ltac2:(tb__ "0|0|
S0S28S5A1SaS46A1S29S5S14S10S5eSeP1SbP14A1Z8A3S9Z0A1A3A1S2aS5S41SaS43A1A3A3A3").
Proof using . reflexivity. Qed.

Lemma bne_holds : ltac2:(tb__ "0|1|
S6SdS3S8R2S10S5eR1S9Z0M0A1A3A2S4S0S1aS22Q40S7R2R1A2A2G0A3A1A2Fa;Frho;").
Proof using .
  intros rho a. cbn [holds branch_taken]. unfold bv_eqb. cbn [eval]. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 0) with 0. rewrite Bool.negb_true_iff, Z.eqb_neq. tauto.
Qed.

Lemma X_env0 : ltac2:(tb__ "0|0|
S6S25R1A1S38S5S8R2A1SaS45A1A3S38S5S8S59R3S4aA2A1S41A3F_;F_;Frho;").
Proof using ENVC HJ Hent Hinp argv.
  intros rho Hg HF. rewrite E_env0_facts in HF.
  destruct (env_leaf_facts rho _ _ Hg HF) as (H0 & Hr & Hm & Hb).
  apply bne_holds in H0.
  pose proof (env_load rho Hg _ eq_refl Hr Hm) as HL.
  assert (Hlt : bv_unsigned (rw rho 20) + 8 <= 8 * ENVC).
  { apply Z.mod_divide in Hm; [|lia]. destruct Hm as [k Hk].
    assert (8 * ENVC mod 8 = 0) by (rewrite Z.mul_comm; apply Z_mod_mult). nia. }
  assert (G' : G (rho_sub rho s_env0)) by (eapply G_stable; [exact Hg|]; apply rho_sub_agree; reflexivity).
  assert (E20 : bv_unsigned (rw (rho_sub rho s_env0) 20) = bv_unsigned (rw rho 20) + 8).
  { cbn -[eval Z.add]. apply (add_lit_small rho (SVar 20) 8); [reflexivity|lia|]. rewrite pow64. lia. }
  unfold F_env. repeat apply Forall_cons; try apply Forall_nil; cbn [holds].
  - rewrite (sll3_val _ G'). change (eval (rho_sub rho s_env0) (SVar 20)) with (rw (rho_sub rho s_env0) 20). rewrite E20. lia.
  - change (eval (rho_sub rho s_env0) (SVar 20)) with (rw (rho_sub rho s_env0) 20). rewrite E20.
    cbn [eval]. rewrite Z_to_bv_unsigned. change (bv_wrap 64 2048) with 2048. lia.
  - apply bv_eq. rewrite and7_val. change (eval (rho_sub rho s_env0) (SVar 20)) with (rw (rho_sub rho s_env0) 20).
    rewrite E20. cbn [eval]. rewrite Z_to_bv_unsigned. change (bv_wrap 64 0) with 0.
    rewrite <- Zplus_mod_idemp_l, Hm. reflexivity.
Qed.

Lemma U_add2 : ltac2:(tb__ "0|1|
S6SdSdS1aS1aS0S1aS22Q40M0S7R5R4A2A2R2A3S0S1aS22G0S7R6R4A2A2R2A3S32S31R4R3A2S34Z2Z40A2A2S0S1aS22G0S7R8SfS5dR7R6A3A2A2S31R5R4A2A3F_;F_;F_;Fy;Fx;Fb;Fa;Frho;").
Proof using ENVC.
  intros rho a b x y Hx Hy Hb. pose proof (urange (eval rho a)). pose proof (urange (eval rho b)).
  cbn [eval]. unfold alu64, alu. rewrite bv_add_unsigned, Hx, Hy.
  unfold bv_wrap. rewrite mod64. apply Z.mod_small. lia.
Qed.

Lemma U_lit' : ltac2:(tb__ "0|0|
S6S1aS1S30Z0R1A2S32R1S34Z2Z40A2A2A2S0S1aS22Q40S7R3S9R2A1A2A2R2A3F_;Fz;Frho;").
Proof using . intros rho z Hz. cbn [eval]. apply Z_to_bv_small. rewrite mod64. exact Hz. Qed.

Lemma S0_facts_v1v2 : ltac2:(tb__ "0|1|
S6S28S5A1S38S5S8R2A1S2aS5SaS43A1R1A3A3S1S30S22Q40M0ScR3P1A2A2S34Z2Z2fA2A2S30S22G0ScR3P2A2A2Z400A2A2F_;Ffs;Frho;").
Proof using ENVC.
  intros rho fs HF. cbn [ss_facts S0_U_lit app] in HF.
  apply Forall_cons_iff in HF as [_ HF]. apply Forall_cons_iff in HF as [_ HF].
  apply Forall_cons_iff in HF as [Hv1 HF]. apply Forall_cons_iff in HF as [_ HF]. apply Forall_cons_iff in HF as [Hv2 _].
  cbn [holds eval] in Hv1, Hv2. rewrite !Z_to_bv_unsigned in Hv1, Hv2.
  change (bv_wrap 64 140737488355104) with 140737488355104 in Hv1. change (bv_wrap 64 1024) with 1024 in Hv2.
  change (2 ^ 47) with 140737488355328. lia.
Qed.

Lemma X_env1 : ltac2:(tb__ "0|0|
S28S56A1S57OF_;F_;S6S3cS25R2A1S39S1cR4S46R3R2A5S39S1cR5S50R4R3A5F_;F_;Fw;Frho;FK;").
Proof using ENVC HJ Hent Hinp argv.
  intros K rho w Hg Hsp.
  pose proof (SP_facts segsU K E_env1 rho w Hsp) as HF. rewrite E_env1_facts in HF.
  pose proof HF as HF0.
  destruct (env_leaf_facts rho _ _ Hg HF) as (H0 & Hr & Hm & Hb).
  change (~ holds rho (SPBranch BC_NE (SLBytes 1 (SVar 20) 8) (SLit 0))) in H0. rewrite bne_holds in H0.
  pose proof (env_load rho Hg _ eq_refl Hr Hm) as HL.
  assert (E : bv_unsigned (rw rho 20) = 8 * ENVC) by (apply HL; pose proof (urange (eval rho (SLBytes 1 (SVar 20) 8))); lia).
  apply Forall_cons_iff in HF0 as [_ HF0]. apply Forall_app in HF0 as [_ HF0].
  destruct (S0_facts_v1v2 rho [] ltac:(rewrite app_nil_r; exact HF0)) as [Hv1 Hv2].
  pose proof ENVC_bound.
  assert (A2 : bv_unsigned (eval rho (SAlu ALU_SLL (SVar 2) (SLit 3))) = 8 * bv_unsigned (rw rho 2)).
  { cbn [eval]. rewrite sll_val. change (3 mod 64) with 3. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
    rewrite Z.mod_small; [lia|]. rewrite pow64. pose proof (urange (rw rho 2)). lia. }
  pose proof (sll3_val rho Hg) as A3.
  assert (D : eval rho e_auxp_leaf = eval rho e_auxp).
  { apply bv_eq. unfold e_auxp_leaf, e_auxp. rewrite ?pow64 in *. change (2 ^ 47) with 140737488355328 in Hv1.
    erewrite (U_add2 rho _ _ (bv_unsigned (rw rho 1) + 8 * bv_unsigned (rw rho 2) + 16 + 8 * ENVC) 8);
      [| | apply U_lit'; lia | lia].
    2:{ erewrite (U_add2 rho _ _ (bv_unsigned (rw rho 1) + 8 * bv_unsigned (rw rho 2) + 16) (8 * ENVC));
          [reflexivity | | cbn [eval]; exact E | lia].
        erewrite (U_add2 rho _ _ (bv_unsigned (rw rho 1) + 8 * bv_unsigned (rw rho 2)) 16); [reflexivity | | apply U_lit'; lia | lia].
        apply (U_add2 rho _ _ (bv_unsigned (rw rho 1)) (8 * bv_unsigned (rw rho 2))); [reflexivity | exact A2 | lia]. }
    erewrite (U_add2 rho _ _ (bv_unsigned (rw rho 1) + 8 * bv_unsigned (rw rho 2) + 8 * ENVC) 24);
      [lia | | apply U_lit'; lia | lia].
    erewrite (U_add2 rho _ _ (bv_unsigned (rw rho 1) + 8 * bv_unsigned (rw rho 2)) (8 * ENVC)); [reflexivity | | exact A3 | lia].
    apply (U_add2 rho _ _ (bv_unsigned (rw rho 1)) (8 * bv_unsigned (rw rho 2))); [reflexivity | exact A2 | lia]. }
  eapply (SP_restate segsU K rho E_env1 S_aux w); [reflexivity | apply diff_env1 | | constructor | exact Hsp].
  repeat constructor; exact D.
Qed.

Lemma E_pn_slash_facts : ltac2:(tb__ "0|0|
S0S28S5A1SaS48A1S29S5S10S5fS11S2dQ8SeP2SbP15A1Z1A3A3S9Z2fA1A3S2aS5S40SaS43A1A3A3A3").
Proof using . reflexivity. Qed.
Lemma E_pn_other_facts : ltac2:(tb__ "0|1|
S0S28S5A1SaS47A1S29S5S10S5eS11S2dQ8SeP2SbP15A1Z1A3A3M0S9Z0A1A3S29S5S14S10S5fG0S9Z2fA1A3A1S2aS5S40SaS43A1A3A3A3A3").
Proof using . reflexivity. Qed.

Lemma X_pn : ltac2:(tb__ "0|3|
S6S5cS25R2A1S4S0S1aS22Q40S7R3S11S2dQ8SeP2SbP15M0A1M1Z1M2A3A3A2A2Z0A3A1S38S5S8R4A1S40A3S0SdS5aR4G0A2SfS5dG1S9G2A1A3A3S1bS71R1P14A2S0SdS5aR7R2A2SbR2A1A3F_;Fi;S38S5S8S59R7R6A2A1S40A3F_;F_;F_;F_;F_;Fs;Frho;").
Proof using ENVC HJ Hinp argv0.
  intros rho s Hg Hnz HF Hs21 Hsid.
  unfold F_pn in HF. apply Forall_cons_iff in HF as [H1 HF]. apply Forall_cons_iff in HF as [H2 _].
  cbn [holds eval] in H1, H2. rewrite (G_rw5 rho Hg) in H1. rewrite Z_to_bv_unsigned in H2. change (bv_wrap 64 131071) with 131071 in H2.
  pose proof (urange (rw rho 21)) as R21.
  pose proof (pn_load rho Hg _ eq_refl ltac:(lia)) as HL.
  assert (Hlt : bv_unsigned (rw rho 21) < Z.of_nat (length argv0)) by lia.
  pose proof len0_bound.
  assert (E21 : bv_unsigned (rw (rho_sub rho s) 21) = bv_unsigned (rw rho 21) + 1).
  { cbn -[eval Z.add]. rewrite Hs21. apply (add_lit_small rho (SVar 21) 1); [reflexivity|lia|]. rewrite pow64. lia. }
  assert (E5 : rw (rho_sub rho s) 5 = rw rho 5) by (cbn; rewrite Hsid by reflexivity; reflexivity).
  unfold F_pn. repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval].
  - rewrite E21, E5, (G_rw5 rho Hg). lia.
  - rewrite E21, Z_to_bv_unsigned. change (bv_wrap 64 131071) with 131071. lia.
Qed.

Lemma X_pn_slash : ltac2:(tb__ "0|0|
S6S25R1A1S38S5S8R2A1SaS48A1A3S38S5S8S59R3S4cA2A1S40A3F_;F_;Frho;").
Proof using ENVC HJ Hinp argv0.
  intros rho Hg HF. rewrite E_pn_slash_facts in HF.
  apply Forall_cons_iff in HF as [H0 HF]. apply Forall_app in HF as [HF _].
  apply (X_pn rho s_pn_slash Hg); [ | exact HF | reflexivity | ].
  - cbn [holds branch_taken] in H0. unfold bv_eqb in H0. apply Z.eqb_eq in H0.
    cbn [eval] in H0 |- *. rewrite H0, Z_to_bv_unsigned. cbv. discriminate.
  - intros i Hi. unfold s_pn_slash, wsub_get.
    destruct (Pos.eqb_spec i 23); [lia|]. destruct (Pos.eqb_spec i 22); [lia|]. destruct (Pos.eqb_spec i 21); [lia|]. reflexivity.
Qed.

Lemma X_pn_other : ltac2:(tb__ "0|0|
S6S25R1A1S38S5S8R2A1SaS47A1A3S38S5S8S59R3S4bA2A1S40A3F_;F_;Frho;").
Proof using ENVC HJ Hinp argv0.
  intros rho Hg HF. rewrite E_pn_other_facts in HF.
  apply Forall_cons_iff in HF as [H0 HF]. apply Forall_cons_iff in HF as [_ HF]. apply Forall_app in HF as [HF _].
  apply (X_pn rho s_pn_other Hg); [ | exact HF | reflexivity | ].
  - apply bne_holds. exact H0.
  - intros i Hi. unfold s_pn_other, wsub_get.
    destruct (Pos.eqb_spec i 23); [lia|]. destruct (Pos.eqb_spec i 22); [lia|]. destruct (Pos.eqb_spec i 21); [lia|]. reflexivity.
Qed.

Definition Q_ecall (K : list event -> Model -> Prop) : assn := ltac2:(tb__ "0|0|
S3cS2S6S6S1S25R1A1S39S1cVK;S42R1R2A5A2Lrho;A2Lw;").

Lemma wsub_id_env0 : ltac2:(tb__ "0|0|
S0S2bS5bS4aS44A2S2cA3"). Proof using . reflexivity. Qed.
Lemma wsub_id_pn_slash : ltac2:(tb__ "0|0|
S0S2bS5bS4cS44A2S2cA3"). Proof using . reflexivity. Qed.
Lemma wsub_id_pn_other : ltac2:(tb__ "0|0|
S0S2bS5bS4bS44A2S2cA3"). Proof using . reflexivity. Qed.
Lemma F_env_below : ltac2:(tb__ "0|0|
S0S2bS65S5S13S16S4dA1A1S41A3S2cA3"). Proof using . reflexivity. Qed.
Lemma F_pn_below : ltac2:(tb__ "0|0|
S0S2bS65S5S13S16S4eA1A1S40A3S2cA3"). Proof using . reflexivity. Qed.
Lemma cuts_start_strict : ltac2:(tb__ "0|0|
S0S2bS66S19S18S52A3S2dA3"). Proof using . reflexivity. Qed.

Lemma phase1 : ltac2:(tb__ "0|0|
S3cOF_;S28S56A1S57OF_;F_;S3aS1cR2R1A3S3eS1cR3S39S1cR2S1dVrhoI;A4S27R2A1A4F_;FK;Fok;").
Proof using ENVC HJ Hent Hinp argv0.
  intros ok K Hok. rewrite S0_U_lit_eq.
  apply (cfg_sound segsU FUEL_START cutpcs_start GSTART cuts_start exits_start G ok K (Q_ecall K) Hok).
  - rewrite cuts_start_strict. intros; discriminate.
  - apply G_stable.
  - apply check_start_U.
  - intros E rho HinE Hg.
    destruct HinE as [<-|[<-|[<-|[<-|[<-|[]]]]]].
    +
      eapply (exit_reenter_G segsU ok K G GSTART cuts_start (Q_ecall K) E_env0 C_env0 F_env s_env0);
        [ right; left; symmetry; apply C_env_eq | apply ent_env0 | apply wsub_id_env0 | apply G_stable
        | apply F_env_below | apply X_env0 | exact Hg].
    +
      eapply triple_conseq; [ | intros w Hw; exact Hw | apply triple_refl].
      intros w Hsp. left. exists S_aux, rho. split; [right; right; left; reflexivity|]. split; [exact Hg|].
      apply X_env1; assumption.
    + eapply (exit_reenter_G segsU ok K G GSTART cuts_start (Q_ecall K) E_pn_slash C_pn0 F_pn s_pn_slash);
        [ right; right; right; left; symmetry; apply C_pn_eq | apply ent_pn_slash | apply wsub_id_pn_slash | apply G_stable
        | apply F_pn_below | apply X_pn_slash | exact Hg].
    + eapply (exit_reenter_G segsU ok K G GSTART cuts_start (Q_ecall K) E_pn_other C_pn0 F_pn s_pn_other);
        [ right; right; right; left; symmetry; apply C_pn_eq | apply ent_pn_other | apply wsub_id_pn_other | apply G_stable
        | apply F_pn_below | apply X_pn_other | exact Hg].
    +
      eapply triple_conseq; [ | intros w Hw; exact Hw | apply triple_refl].
      intros w Hsp. right. exists rho. auto.
  - left; reflexivity.
  - apply G_rhoI.
Qed.

Lemma E_ecall_a7 : ltac2:(tb__ "0|1|
S6S0S23Q40M0A1S7R1S17S42Z11A2A2S24G0Z60A2A3Frho;").
Proof using . reflexivity. Qed.
Lemma F_tid_below : ltac2:(tb__ "0|0|
S0S2bS65S5S13P19A1S4fA3S2cA3"). Proof using . reflexivity. Qed.
Lemma PID_MAX_val : PID_MAX_ENVELOPE = 4194304. Proof using . reflexivity. Qed.

Lemma phase2 : ltac2:(tb__ "0|1|
S3cOF_;S6S67S1cR2S62Vm0;A1M0A3S3aS1cR3G0A3S25R3A1S3fS1cR5S39S1cG0S42R4A4S3cS2S6S6S1S12P18R6R1A3S39S1cS63Vm0;A1S49R1R2A5A2Lrho';A2Lw;A4F_;F_;F_;Frho;Fok;").
Proof using ENVC brk lim mb sp.
  intros ok rho Hokp Hokf Hg.
  apply triple1_ecall_det; [exact Hokf | apply ecall_at_U |].
  intros tr ms md Hsp [Htr Hmd]. subst tr md.
  pose proof (smatch_pending_pending _ _ _ _ _ _ Hsp) as Hp. rewrite E_ecall_a7 in Hp.
  pose proof (smatch_pending_halted _ _ _ _ _ _ Hsp) as Hidle.
  assert (H96 : bv_unsigned (Z_to_bv 64 96) = 96) by reflexivity.
  split.
  - eapply Hokp; [split; reflexivity | exact Hp |]. apply set_tid_fresh_only_ok; [exact Hidle | exact H96 | apply m0_tid].
  - intros w' Hw.
    destruct (wstep_set_tid_fresh_inv Hp Hidle H96 m0_tid Hw) as (tid & Htid & ->).
    exists (rho_set_rw rho 24 tid). split; [apply agree_below_set_rw; lia|].
    split.
    + rewrite S_tid_eq. apply smatch_add_facts; [ | | apply F_tid_below].
      * apply (smatch_after_ret segsU rho E_ecall [] ms m0); [exact Hsp | apply with_tid_idle; apply m0_idle].
      * unfold F_tid. rewrite PID_MAX_val in Htid.
        repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval rw rho_set_rw]; rewrite Pos.eqb_refl;
          rewrite Z_to_bv_unsigned; [change (bv_wrap 64 1) with 1 | change (bv_wrap 64 4194304) with 4194304]; lia.
    + split; [reflexivity|]. exists tid. split; [exact Htid | reflexivity].
Qed.

Theorem start_sum_U : ltac2:(tb__ "0|2|
S3cOF_;S3aS1cR1S62Vm0;A1M0A3S67S1cR2G0A3S3aS1cR3S63Vm0;A1M1A3S3eS1cR4S39S1cG0S1dVrhoI;A4S3bS1cG1P14VrhoI;S64A5A4F_;F_;F_;Fok;").
Proof using ENVC HJ Hent Hinp argv0 lim.
  intros ok Hok0 Hokp Hok1.
  eapply triple_seq; [apply phase1; exact Hok0|].
  unfold Q_ecall. apply triple_ex; intros rho. apply triple_pure; intros Hg.
  eapply triple_seq; [apply triple1_triple; apply phase2; assumption|].
  apply triple_ex; intros rho'. apply triple_pure; intros Hag.
  eapply triple_conseq; [intros w Hw; exact Hw | | apply triple1_triple; eapply sym_run_sound;
    [apply run_tid_U | exact Hok1 | intros Hl; discriminate]].
  intros w Hw. eapply LQ_weaken; [ | | intros L HL; exact HL | exact Hw].
  - cbv. discriminate.
  - eapply agree_below_trans; [exact Hg|]. eapply agree_below_le; [|exact Hag]. cbv. discriminate.
Qed.

Definition QE_ecall (K : list event -> Model -> Prop) : world -> Prop := ltac2:(tb__ "0|0|
S3cS2S6S6S1S25R1A1S39S1cVK;S42R1R2A5A2Lrho;A2Lw;").

Lemma var_bound_env : ltac2:(tb__ "0|2|
S6S28S5A1S5S25R3A1S38S5S8R4A1S29S5R2S2aS5S41R3A3A3A3S1S0S1aS22Q40M0S7R5S53A2A2S31S22G0ScR5P14A2A2Z8A2M1A3S30G1Z808A2A2F_;F_;Ff0;Ffs;Frho;").
Proof using ENVC HJ Hinp.
  intros rho fs f0 Hg HF. destruct (env_leaf_facts rho _ _ Hg HF) as (_ & Hr & _ & Hb).
  split; [|lia]. unfold var_envx. apply (add_lit_small rho (SVar 20) 8); [reflexivity|lia|]. rewrite pow64. lia.
Qed.

Lemma pn_var_ok : ltac2:(tb__ "0|2|
S6S5cS38S5S8R2A1S40A3S0SdS5aR2P15M0A2SfS5dSbG0A1S9Z1A1A3A3S30S22Q40M1S7R4S55A2A2S22G1S7S59R4R3A2S54A2A2A2F_;F_;Fs;Fr;").
Proof using ENVC.
  intros r s HF Hs. unfold F_pn in HF. apply Forall_cons_iff in HF as [_ HF]. apply Forall_cons_iff in HF as [H2 _].
  cbn [holds eval] in H2. rewrite Z_to_bv_unsigned in H2. change (bv_wrap 64 131071) with 131071 in H2.
  unfold var_pnx, var_pn.
  rewrite (add_lit_small r (SVar 21) 8193 (bv_unsigned (rw r 21))); [ | reflexivity | lia | rewrite pow64; lia].
  rewrite (add_lit_small (rho_sub r s) (SVar 21) 8192 (bv_unsigned (rw r 21) + 1)); [lia | | lia | rewrite pow64; lia].
  change (eval (rho_sub r s) (SVar 21)) with (rw (rho_sub r s) 21). cbn -[eval Z.add]. rewrite Hs.
  apply (add_lit_small r (SVar 21) 1); [reflexivity | lia | rewrite pow64; lia].
Qed.

Lemma ephase1 : ltac2:(tb__ "0|0|
S28S56A1S57OF_;F_;S3dS1cS39S1cR1S1dVrhoI;A4S26R1A1A3FK;").
Proof using ENVC HJ Hent Hinp argv0 m0.
  intros K. rewrite S0_U_lit_eq.
  change S0_U_lit with (vn_state (mkVN S0_U_lit 200 (SLit 0))).
  apply (cfg_complete_autoI segsU FUEL_START cutpcs_start GSTART vcuts_start vexits_start G K (QE_ecall K)).
  - apply G_stable.
  - apply echeck_start_U.
  - intros E rho HinE Hg.
    destruct HinE as [<-|[<-|[<-|[<-|[<-|[]]]]]].
    + eapply (eexit_reenter_I segsU K G GSTART vcuts_start (QE_ecall K) (mkVN E_env0 150 var_envx) (mkVN C_env 100 var_env) F_env C_env0 s_env0);
        [ right; left; reflexivity | apply C_env_eq | apply ent_env0 | apply wsub_id_env0 | apply G_stable
        | apply F_env_below | | cbn; lia | cbn; lia | exact Hg].
      intros r Hgr HF. split; [apply X_env0; assumption|].
      cbn [vn_var vn_state] in *. rewrite E_env0_facts in HF.
      destruct (var_bound_env r _ _ Hgr HF) as [-> _].
      unfold var_env. change (eval (rho_sub r s_env0) (SVar 20)) with (eval r (SAlu ALU_ADD (SVar 20) (SLit 8))).
      destruct (env_leaf_facts r _ _ Hgr HF) as (_ & Hr & _ & Hb).
      rewrite (add_lit_small r (SVar 20) 8 (bv_unsigned (rw r 20))); [lia|reflexivity|lia|rewrite pow64; lia].
    +
      intros w Hsp. exists w. split; [apply wsteps_refl|]. left.
      exists (to_enodeI G (mkVN S_aux 90 (SLit 4096))), rho.
      split; [apply in_map; right; right; left; reflexivity|].
      cbn [to_enodeI en_state en_ghost en_meas fst snd vn_state]. split; [exact Hg|]. split; [apply X_env1; assumption|].
      unfold vmeasI. cbn [vn_var vn_rank].
      pose proof (SP_facts segsU K E_env1 rho w Hsp) as HF. rewrite E_env1_facts in HF.
      destruct (var_bound_env rho _ _ Hg HF) as [-> Hb].
      rewrite (U_lit' rho 4096) by (rewrite pow64; lia). pose proof (urange (rw rho 20)). rewrite pow64. lia.
    + eapply (eexit_reenter_I segsU K G GSTART vcuts_start (QE_ecall K) (mkVN E_pn_slash 150 var_pnx) (mkVN C_pn 80 var_pn) F_pn C_pn0 s_pn_slash);
        [ right; right; right; left; reflexivity | apply C_pn_eq | apply ent_pn_slash | apply wsub_id_pn_slash | apply G_stable
        | apply F_pn_below | | cbn; lia | cbn; lia | exact Hg].
      intros r Hgr HF. split; [apply X_pn_slash; assumption|].
      cbn [vn_var vn_state] in *. rewrite E_pn_slash_facts in HF.
      apply Forall_cons_iff in HF as [_ HF]. apply Forall_app in HF as [HF _]. apply (pn_var_ok r s_pn_slash HF); reflexivity.
    + eapply (eexit_reenter_I segsU K G GSTART vcuts_start (QE_ecall K) (mkVN E_pn_other 150 var_pnx) (mkVN C_pn 80 var_pn) F_pn C_pn0 s_pn_other);
        [ right; right; right; left; reflexivity | apply C_pn_eq | apply ent_pn_other | apply wsub_id_pn_other | apply G_stable
        | apply F_pn_below | | cbn; lia | cbn; lia | exact Hg].
      intros r Hgr HF. split; [apply X_pn_other; assumption|].
      cbn [vn_var vn_state] in *. rewrite E_pn_other_facts in HF.
      apply Forall_cons_iff in HF as [_ HF]. apply Forall_cons_iff in HF as [_ HF]. apply Forall_app in HF as [HF _].
      apply (pn_var_ok r s_pn_other HF); reflexivity.
    + intros w Hsp. exists w. split; [apply wsteps_refl|]. right. exists rho. auto.
  - left; reflexivity.
  - apply G_rhoI.
Qed.

Lemma ephase2 : ltac2:(tb__ "0|0|
S6S25R1A1S3dS1cS39S1cS62Vm0;A1S42R2A4S3cS2S6S6S1S12P18R4R1A3S39S1cS63Vm0;A1S49R1R2A5A2Lrho';A2Lw;A3F_;Frho;").
Proof using ENVC brk lim mb sp.
  intros rho Hg.
  apply etriple_ecall_det; [apply ecall_at_U |].
  intros tr ms md Hsp [Htr Hmd]. subst tr md.
  pose proof (smatch_pending_pending _ _ _ _ _ _ Hsp) as Hp. rewrite E_ecall_a7 in Hp.
  pose proof (smatch_pending_halted _ _ _ _ _ _ Hsp) as Hidle.
  assert (H96 : bv_unsigned (Z_to_bv 64 96) = 96) by reflexivity.
  exists ([], mkCfg (after_sys ms (Z_to_bv 64 1)) (with_tid (Z_to_bv 64 1) m0)). split.
  - apply (@wstep_set_tid_fresh_intro segsU [] _ _ _ _ Hp Hidle H96 m0_tid). apply tid_one_ok.
  - exists (rho_set_rw rho 24 (Z_to_bv 64 1)). split; [apply agree_below_set_rw; lia|].
    split.
    + rewrite S_tid_eq. apply smatch_add_facts; [ | | apply F_tid_below].
      * apply (smatch_after_ret segsU rho E_ecall [] ms m0); [exact Hsp | apply with_tid_idle; apply m0_idle].
      * unfold F_tid.
        repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval rw rho_set_rw]; rewrite Pos.eqb_refl;
          rewrite !Z_to_bv_unsigned; cbv; [discriminate|reflexivity].
    + split; [reflexivity|]. exists (Z_to_bv 64 1). split; [apply tid_one_ok | reflexivity].
Qed.

Theorem start_sum_ex_U : ltac2:(tb__ "0|0|
S3dS1cS39S1cS62Vm0;A1S1dVrhoI;A4S3bS1cS63Vm0;A1P14VrhoI;S64A5A3").
Proof using ENVC HJ Hent Hinp argv0 lim.
  eapply etriple_seq; [apply ephase1|].
  unfold QE_ecall. apply etriple_ex; intros rho. intros w [Hg Hsp]. revert w Hsp.
  change (etriple segsU (SP segsU (K0 m0) E_ecall rho) (LQ segsU (K1 m0) 20 rhoI Posts_start)).
  eapply etriple_seq; [apply ephase2; exact Hg|].
  apply etriple_ex; intros rho'. intros w [Hag Hsp].
  destruct (sym_run_complete segsU FUEL_START [0x13484] S_tid [mkLeaf S_main RsCut] (K1 m0) rho' w eq_refl run_tid_U Hsp)
    as (L & rho'' & w' & HinL & Hsteps & Hag' & Hsp').
  exists w'. split; [exact Hsteps|].
  destruct HinL as [<-|[]].
  exists (mkLeaf S_main RsCut), rho''. split; [left; reflexivity|]. split.
  - eapply agree_below_trans; [exact Hg|]. eapply agree_below_le; [| eapply agree_below_trans; [exact Hag| eapply agree_below_le; [|exact Hag']]]; cbv; discriminate.
  - exact Hsp'.
Qed.

End Start.
