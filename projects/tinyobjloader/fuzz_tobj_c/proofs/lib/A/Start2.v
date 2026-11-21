(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the segment runs on the states A/StartRegenS.v computes per CONFIG_RSEQ, a section flag, with the run, check and restatement lemmas of A/StartRegen.v, its statements written as plain text; the NULL-hint mmap witnesses are Linux's own address, place_ok_linux, written as plain text; the reserved ledger is the image's entries then the vDSO/vvar pair). *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "nil"; "cons"; "list"; "prod"; "true"; "bool"; "Some"; "option"; "pair"; "app"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@Corelib.Init.Logic"; "eq"; "ex"; "and"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "SLit"; "sprop"; "rw"; "SAlu"; "agree_below"; "holds"; "SPBranch"; "SPNot"; "SVar"; "ss_facts"; "swf"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "ok_frameA"; "LQA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e0.Start1States"; "E_s2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "mkLeafA"; "axst"; "sym_runA"; "mkAX"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "event"; "Model"; "vm_init_sp"; "vm_reserved"; "vm_limit"; "vm_maps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA"; "KxA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "triple1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e0.Start2States"; "S_hm2"; "SPIN5"; "S_s2x"; "T_hm2"; "E_s3"; "@LinuxProcessSemantics.Riscv.Sem"; "alu64"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start2.Seg2"; "n5"; "Post2"; "m5"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes"; "eager_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok_none"; "@Stdlib.ZArith.BinInt.Z"; "add"; "modulo"; "le"; "pow"; "sub"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_AND"; "ALU_OR"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start2"; "ECALL_MMAP"; "FUEL2"; "G2"; "HMCUT"; "MF2"; "SPIN_MMAPORDIE"; "S_s2fail"; "sd_hm2"; "Xhm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib"; "cfg1_okA"; "SHB"; "objs_clear_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "RsSymJump"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "segments_reserved"; "@LinuxProcessSemantics.Riscv.Prelude"; "bv_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "band_covered"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartHm"; "smear_sv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap"; "S_ret_lit"; "enomem_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall Glue3 SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt LedgerA StepA SoundA EntailA CompleteA GlueA SysCallA MmapA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts StartLib KxA Placement PlacementA SysSpecStart.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require SysStartA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartHm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartRegenS StartRegen.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.PlacementA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.SysSpecStart OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.SysStartA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartHm.
(* LPS 727298f3: this segment's states are those A/StartRegenS.v computes per CONFIG_RSEQ
   (Start1R's exit [E_s2 r], Start2R's states), and its runs, checks and restatement those
   A/StartRegen.v proves of them for both values. *)
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartRegenS.Start1R OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartRegenS.Start2R OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartRegen.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

(* [S_s2x r] is [E_s2 r]'s grant with the memset test's fact (A/StartRegenS.v, Start2R). *)
Lemma S_s2x_eq : forall r, S_s2x r = ax_add_facts [MF2] (eager_ok (E_s2 r) 65536 28%positive).
Proof. intros [|]; reflexivity. Qed.

Lemma memset_test_ne : ltac2:(tb__ "0|2|
S1fQ40M0A1SeS0S45S20G0R1A2Z10A2Z0M1A3SeS7S5eG0S3eS4aS3eS4bS21G0Z120A2S3eS49R2S21G0N248A2A3A3S21G0ZfA2A3S21G0G1A2A3ScA3F_;Fv;").
Proof.
  intros v Hv. pose proof (bv_unsigned_in_range _ v) as R. change (bv_modulus 64) with 18446744073709551616 in R.
  unfold bv_eqb. apply Z.eqb_neq.
  unfold alu64, alu. rewrite bv_and_unsigned, bv_or_unsigned, bv_add_unsigned, !Z_to_bv_unsigned.
  change (bv_wrap 64 288) with 288. change (bv_wrap 64 15) with 15. change (bv_wrap 64 0) with 0.
  change (bv_wrap 64 (-584)) with 18446744073709551032.
  unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616.
  set (y := (bv_unsigned v + 18446744073709551032) mod 18446744073709551616).
  assert (Ypos : 0 <= y) by (subst y; apply Z.mod_pos_bound; lia).
  assert (Hy : y mod 16 = 8).
  { subst y. destruct (Z.mod_divide (bv_unsigned v) 16) as [Hd _]; [lia|]. destruct (Hd Hv) as [q Hq].
    rewrite Hq.
    match goal with |- ?a mod _ mod 16 = 8 =>
      rewrite (Zdiv.Zmod_eq_full a 18446744073709551616) by lia;
      set (d := a / 18446744073709551616) end.
    match goal with |- ?a mod 16 = 8 =>
      replace a with (8 + (q + 1152921504606846939 - d * 1152921504606846976) * 16) by lia end.
    rewrite Z.mod_add by lia. reflexivity. }
  rewrite Z.land_lor_distr_l. change (Z.land 288 15) with 0. rewrite Z.lor_0_l.
  change 15 with (Z.ones 4). rewrite Z.land_ones by lia. change (2 ^ 4) with 16. lia.
Qed.

Lemma MF2_holds : forall rho : valuation, bv_unsigned (rw rho 1%positive) mod 16 = 0 -> holds rho MF2.
Proof.
  intros rho H16. cbn [holds MF2]. unfold branch_taken. cbn [eval]. rewrite (memset_test_ne (rw rho 1%positive) H16). discriminate.
Qed.

Section Seg2.

Variables (m : Model) (B : Z).
(* LPS 727298f3: the start state is made per CONFIG_RSEQ (StartStates.v), and with it every state
   of this segment (A/StartRegenS.v); [rq] is this run's value, the launch's
   [kb_rseq (in_kernel inp)] (StartMain.v).  A computation over a state destructs [rq] first. *)
Variable rq : bool.
Ltac rvmc := destruct rq; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Ltac rrefl := destruct rq; reflexivity.
(* LPS 727298f3: the reserved ledger is the image's entries then the vDSO/vvar pair (Fw/SysSpec.v [vdso_pair_ok]). *)
Hypothesis Hres : exists V, vm_reserved (m_vmmaps m) = segments_reserved segsA ++ V /\ vdso_pair_ok V.
Hypothesis Htop : init_sp_ok (m_vmmaps m).
Hypothesis Hband : ltac2:(tb__ "0|2|
S61SbS5S1fQ40A1M0G0A2S31S2dVm;A1M1A1S33G1A1A3S60S5fA3").
Hypothesis HBlim : ltac2:(tb__ "0|0|
S46S44VB;Z10000A2S32S2dVm;A1A1A2").

Variable ok : assn.
Hypothesis OKF : ltac2:(tb__ "0|1|
S23S12S4S1fQ40A1A1S4S2eA1M0S2fR5R4R3R2R1A4SeG0R3S2S2eA1A3F_;Fmd;Ftr;Ftp;Frho;S24SdVok;R2A3F_;FJ;").
Hypothesis OKP : ltac2:(tb__ "0|1|
S23S12S4S1fQ40A1A1S4S2eA1M0S2fR5R4R3R2R1A4SeG0R3S2S2eA1A3F_;Fmd;Ftr;Ftp;Frho;S67SdVok;R2A3F_;FJ;").

Definition n5 : word := Z_to_bv 64 0x10000.

Definition m5 (a : word) : Model := eager_model 0x10000 m a.

Definition Post2 (rho : valuation) : assn :=
  fun w : world => exists (a : bv 64) (rho' : valuation),
    mmap_place_ok_none (Z_to_bv 64 0) m n5 a /\ agree_below 28%positive (rho_set_rw rho 27%positive a) rho' /\
    SPA segsA (KxA (m5 a) (B + 65536)) (E_s3 rq) rho' [] w.

Lemma OKFx : ltac2:(tb__ "0|0|
S2fS0S24SdVok;S34R2R1A2A3FBB;Fmm;").
Proof using OKF. intros. apply OKF. intros; eapply KxA_nil; eassumption. Qed.

Lemma clear_s2 : objs_clear_e [] (ax_S (E_s2 rq)) = true.
Proof. rvmc. Qed.

Lemma sp16_of_facts : forall rho : valuation,
  Forall (holds rho) (ss_facts (ax_S (E_s2 rq))) -> bv_unsigned (rw rho 1%positive) mod 16 = 0.
Proof.
  intros rho HF.
  assert (X : In (SPAlign 1%positive 4) (ss_facts (ax_S (E_s2 rq)))) by (clear HF; destruct rq; vm_compute; tauto).
  pose proof (proj1 (Forall_forall _ _) HF _ X) as H. cbn [holds] in H. change (2 ^ 4) with 16 in H. lia.
Qed.

(* The grant's variable is the next variable of [E_s2 rq] (27 for both values, A/StartRegen.v
   [next_E_s2]), left as [ss_next] here, where the node lemma puts it. *)
Lemma node_s2 : forall rho : valuation,
  bv_unsigned (rw rho 1%positive) = bv_unsigned (vm_init_sp (m_vmmaps m)) ->
  triple1 segsA ok (SPA segsA (KxA m B) (E_s2 rq) rho [])
    (fun w : world => SPA segsA (KxA m B) (S_s2fail rq) rho [] w \/
       exists a : bv 64, mmap_place_ok_none (Z_to_bv 64 0) m n5 a /\
         SPA segsA (KxA (m5 a) (B + 65536)) (eager_ok (E_s2 rq) 65536 28%positive) (rho_set_rw rho (ss_next (ax_S (E_s2 rq))) a) [] w).
Proof using HBlim Hband Hres Htop OKF OKP.
  intros rho Hv1.
  apply (eager_rw_node ok OKF OKP (E_s2 rq) 0x10000 m B [] 28%positive);
    [ rrefl | rrefl | rvmc
    | rvmc | rvmc | rvmc | rvmc
    | rvmc | rvmc | rvmc
    | reflexivity | reflexivity | lia | destruct rq; cbv; reflexivity
    | exact clear_s2 | exact Hres | exact Htop | exact Hband | exact HBlim
    | intros e sz [] | exact Hv1 ].
Qed.

Lemma LQA1_SPA : ltac2:(tb__ "0|1|
S23S1S12S2aS35S25SdR5R4R3S2S1fQ40A1A1M0S3S27S29R2S5bA2S2S27A1A3R1A7SfS12S12S10S18R6R5R1A3S22SdR7R4R1G0R3A6A2Lrho';A2F_;Fw;FE;Frho;Fn;FJ;").
Proof. intros J n rho E w (L & rho' & [<-|[]] & Hag & Hsm & Hk). exists rho'. split; [exact Hag | split; [exact Hsm | exact Hk]]. Qed.

Lemma to_S_s2x : forall (J : jpredA) (rho : valuation) (w : world),
  SPA segsA J (eager_ok (E_s2 rq) 65536 28%positive) rho [] w -> SPA segsA J (S_s2x rq) rho [] w.
Proof.
  intros J rho w [Hsm Hk]. split; [|exact Hk]. rewrite (S_s2x_eq rq). apply smatchA_add_facts; [exact Hsm | | clear Hsm Hk; rvmc].
  apply Forall_cons; [|apply Forall_nil]. apply MF2_holds.
  apply sp16_of_facts. pose proof (SPA_facts_hold segsA _ rho _ [] w (conj Hsm Hk)) as HF.
  cbn [ax_S eager_ok ss_facts add_facts S_after] in HF. apply Forall_app in HF as [_ HF]. exact HF.
Qed.

Theorem start2_sum_A : forall rho : valuation,
  bv_unsigned (rw rho 1%positive) = bv_unsigned (vm_init_sp (m_vmmaps m)) ->
  triple segsA ok (SPA segsA (KxA m B) (E_s2 rq) rho []) (Post2 rho).
Proof using HBlim Hband Hres Htop OKF OKP.
  intros rho Hv1.
  eapply triple_seq; [apply triple1_triple; apply (node_s2 rho Hv1)|].
  apply triple_disj.
  - eapply (fail_arm_safe ok (KxA m B) (OKFx _ _) (fun n => stableA_KxA segsA n m B) (S_s2fail rq) (SPIN5 rq) 400%nat SPIN_MMAPORDIE);
      [ rrefl | rrefl | rrefl | exact (runF_s2 rq) | exact (spin5 rq) ].
  - apply triple_ex; intros a. apply triple_pure; intros Hpl.
    rewrite (next_E_s2 rq).
    set (rho' := rho_set_rw rho 27%positive a). set (J5 := KxA (m5 a) (B + 0x10000)).
    change (eager_model 0x10000 m a) with (m5 a). change (KxA (m5 a) (B + 0x10000)) with J5.
    eapply triple_conseq; [intros w Hw; exact (to_S_s2x J5 rho' w Hw) | intros w Hw; exact Hw |].
    eapply triple_seq; [apply (run_cfg1 ok J5 FUEL2 [HMCUT; ECALL_MMAP] G2 (S_s2x rq) (T_hm2 rq) _ [] (OKFx _ _) (fun n => stableA_KxA segsA n _ _) (check2a rq))|].
    apply triple_ex; intros L. apply triple_ex; intros rho2. apply triple_pure; intros HinL. apply triple_pure; intros Hag2.
    destruct HinL as [<-|[]]. cbn [la_state].
    change (fun w => smatchA segsA rho2 [] (T_hm2 rq) w /\ J5 rho2 [] (w_tr w) (cfg_model (w_cfg w))) with (SPA segsA J5 (T_hm2 rq) rho2 []).
    eapply triple_conseq; [intros w Hw; exact (restate_hm2 rq J5 rho2 w Hw) | | apply (run_cfg1 ok J5 FUEL2 [HMCUT; ECALL_MMAP] G2 (S_hm2 rq) (E_s3 rq) _ [] (OKFx _ _) (fun n => stableA_KxA segsA n _ _) (check2b rq))].
    intros w Hw. destruct (LQA1_SPA J5 G2 rho2 (E_s3 rq) w Hw) as (rho3 & Hag3 & Hsp3).
    exists a, rho3. split; [exact Hpl|]. split; [eapply agree_below_trans; [exact Hag2 | exact Hag3] | exact Hsp3].
Qed.

(* LPS 727298f3: the witness is Linux's own address ([place_ok_linux], Fw/SysSpec.v), where a granted NULL-hint mmap now goes; written as plain text. *)
Hypothesis Hwit : (exists a : stdpp.bitvector.definitions.bv 64, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.place_ok_linux m OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start2.Seg2.n5 a).

Theorem start2_sum_ex_A : forall rho : valuation,
  bv_unsigned (rw rho 1%positive) = bv_unsigned (vm_init_sp (m_vmmaps m)) ->
  etriple segsA (SPA segsA (KxA m B) (E_s2 rq) rho []) (Post2 rho).
Proof using HBlim Hband Hres Htop Hwit.
  intros rho Hv1.
  eapply etriple_seq.
  { apply (eager_rw_enode (E_s2 rq) 0x10000 m B [] 28%positive);
      [ rrefl | rrefl | rvmc
      | rvmc | rvmc | rvmc | rvmc
      | rvmc | rvmc | rvmc
      | reflexivity | reflexivity | lia | destruct rq; cbv; reflexivity
      | exact clear_s2 | exact Hres | exact Htop | exact Hband | exact HBlim | exact Hwit
      | intros e sz [] | exact Hv1 ]. }
  apply etriple_ex; intros a. intros w [Hpl Hsp]. revert w Hsp.
  rewrite (next_E_s2 rq).
  set (rho' := rho_set_rw rho 27%positive a). set (J5 := KxA (m5 a) (B + 0x10000)).
  change (eager_model 0x10000 m a) with (m5 a). change (KxA (m5 a) (B + 0x10000)) with J5.
  change (etriple segsA (SPA segsA J5 (eager_ok (E_s2 rq) 0x10000 28%positive) rho' []) (Post2 rho)).
  eapply etriple_conseq; [intros w Hw; exact (to_S_s2x J5 rho' w Hw) | intros w Hw; exact Hw |].
  eapply etriple_seq; [apply (erun_cfg1 J5 FUEL2 [HMCUT; ECALL_MMAP] G2 (S_s2x rq) (T_hm2 rq) _ [] (fun n => stableA_KxA segsA n _ _) (check2a rq))|].
  apply etriple_ex; intros L. apply etriple_ex; intros rho2. apply etriple_pure; intros HinL. apply etriple_pure; intros Hag2.
  destruct HinL as [<-|[]]. cbn [la_state].
  change (fun w => smatchA segsA rho2 [] (T_hm2 rq) w /\ J5 rho2 [] (w_tr w) (cfg_model (w_cfg w))) with (SPA segsA J5 (T_hm2 rq) rho2 []).
  eapply etriple_conseq; [intros w Hw; exact (restate_hm2 rq J5 rho2 w Hw) | | apply (erun_cfg1 J5 FUEL2 [HMCUT; ECALL_MMAP] G2 (S_hm2 rq) (E_s3 rq) _ [] (fun n => stableA_KxA segsA n _ _) (check2b rq))].
  intros w Hw. destruct (LQA1_SPA J5 G2 rho2 (E_s3 rq) w Hw) as (rho3 & Hag3 & Hsp3).
  exists a, rho3. split; [exact Hpl|]. split; [eapply agree_below_trans; [exact Hag2 | exact Hag3] | exact Hsp3].
Qed.
End Seg2.
