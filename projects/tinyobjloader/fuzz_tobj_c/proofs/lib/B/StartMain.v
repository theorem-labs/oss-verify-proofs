(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "modulo"; "pow"; "divide"; "@Corelib.Init.Datatypes"; "list"; "nil"; "prod"; "None"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "agree_below"; "@Corelib.Numbers.BinNums"; "Z"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "m_fds"; "m_fs"; "m_stdin"; "FdEntry"; "InputStream"; "m_halted"; "m_tid"; "m_vm_lazy"; "m_vm_materialized"; "m_vmmaps"; "sp_window_hi"; "sp_window_lo"; "vm_backing_used"; "vm_brk"; "vm_init_sp"; "vm_limit"; "vm_maps"; "vm_noaccess"; "vm_reserved"; "vm_start_brk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Init"; "pcA"; "phA"; "S0_A"; "c0A"; "imgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState"; "Jinit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start0"; "K0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartLib"; "K_nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartMain.Main"; "M1"; "QMain"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "ok_frame"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "jpredA"; "ok_frameA"; "@LinuxProcessSemantics.LinuxProcessSem.Fs"; "Fs"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "cfg_model"; "mkEntry"; "segments_reserved"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Fork"; "PID_MAX_ENVELOPE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartArgF"; "arg_layout"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartMain"; "B0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartTop"; "PostMain"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "ok_pframe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout"; "valid_entry48"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall SymSummary Glue3 SymHeap SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt LedgerA StepA SoundA EntailA CompleteA GlueA GlueA2 SysCallA
  MmapA MmapFixedA MmapFixedA2 MmapBrkA MmapNodesA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv InitState InitLayout.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Init Code StartLib KxA Placement PlacementA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require StartStates Start0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ne.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Start7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ob.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require os.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Start8M.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require StartTop.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Placement OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.PlacementA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartArgF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start1States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ne.Start1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o5.Start7States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ob.Start8States0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8CallDefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.os.Start8CallA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.os.Start8CallB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start8M OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartTop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition B0 : Z := 0.

Section Main.
Variable sp brk mb : word.
Variable draw : EntryDraw.
Variable lim : Z.
Variable inp : ProcInput.
Hypothesis Hent : ltac2:(tb__ "0|0|
S47S30S3cVsp;Vbrk;Vmb;Vdraw;A4Vinp;A3").
Hypothesis Hinp : valid_input_either inp.
Hypothesis Hlim : 2 ^ 25 <= lim.
Variable rhoI : valuation.
Hypothesis HJ : ltac2:(tb__ "0|0|
S31S3S2cS2dVsp;Vdraw;Vinp;VrhoI;A7").

Let m0 : Model := ltac2:(tb__ "0|0|
S3bS2fVsp;Vbrk;Vmb;Vdraw;Vlim;Vinp;A6A1").

Definition M1 (tid : word) : Model := with_tid tid m0.

Variable ok : assn.
Hypothesis OKF : ltac2:(tb__ "0|0|
SaS16A1S17OF_;F_;S33R1A1S37S3Vok;R2A3F_;FK;").
Hypothesis OKP : ltac2:(tb__ "0|0|
SaS16A1S17OF_;F_;S33R1A1S45S3Vok;R2A3F_;FK;").
Hypothesis OKFA : ltac2:(tb__ "0|1|
S38S10SaS15Q40A1A1SaS16A1M0S17R5R4R3R2R1A4S1G0R3SbS16A1A3F_;Fmd;Ftr;Ftp;Frho;S39S3Vok;R2A3F_;FJ;").
Hypothesis OKPA : ltac2:(tb__ "0|1|
S38S10SaS15Q40A1A1SaS16A1M0S17R5R4R3R2R1A4S1G0R3SbS16A1A3F_;Fmd;Ftr;Ftp;Frho;S46S3Vok;R2A3F_;FJ;").

Lemma K0_nil : K_nil (K0 m0). Proof. intros tr md [H _]; exact H. Qed.
Lemma K1_nil : K_nil (K1 m0). Proof. intros tr md [H _]; exact H. Qed.

Lemma M1_fields : ltac2:(tb__ "0|7|
S15Q40A1M0S0S1SfG0A1M1S1dS34R1A1M2A1SdG0A1A3S0S1SaScG0G0A2M3A1M4S1fG2A1SbG3A1M5A3S0S1SaG0A1S20G2A1SbG0A1A3S0S1G4S2aS21G2A1M6A1S3dS3A1A3S0S1G4S28G6A1G5A3S0S1G4S29G6A1G5A3S0S1S13S27G6A1Vlim;A3S0S1G0S2bG6A1Vbrk;A3S0S1G0S25G6A1Vbrk;A3S0S1G0S26G6A1Vsp;A3S0S1S13S24G2A1Z0A3S0S1G1S1eG2A1SeG0R1A2A3S0S1SaScG0S1bA2A1S18G2A1S18Vm0;A1A3S0S1S3aS19G2A1S19Vm0;A1A3S1S1cS1aG2A1S1aVm0;A1A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2Ftid;").
Proof. clear. intros tid. unfold M1, m0, c0A, init_config, init_model, with_tid. cbn -[segments_reserved]. repeat split; reflexivity. Qed.

Lemma brk_facts : ltac2:(tb__ "0|1|
S0S0S4Z643000S14Q40Vbrk;A2M0A2S4G0Z80643000A2A2S9Z1000G0A2A2").
Proof.
  clear - Hent. destruct Hent as (_ & Hbrk & _ & _). unfold valid_brk in Hbrk. rewrite reserved_top_A in Hbrk.
  unfold IMG_BAND_HI, brk_aslr_max, page_size in Hbrk. split; [lia|]. apply Z.mod_divide; lia.
Qed.
Lemma sp_facts : ltac2:(tb__ "0|1|
S0S0S4S23S14Q40Vsp;A2M0A2S4G0S22A2A2S0S0S4Z7fff80000000G0A2S4G0S8Z2Z2fA2A2A2S1S13S7G0Z10A2Z0A3A2A2").
Proof.
  clear - Hent Hinp. destruct Hent as (Hsp & _ & _ & Hfit). pose proof (nums sp inp Hsp Hinp) as N. cbv zeta in N. destruct N as (Nsp & N16 & _).
  pose proof (LEN_fit sp inp Hinp Hfit) as LF. rewrite sp_hi_val in LF. pose proof (Zle_0_nat (img_len (in_argv inp) (in_envp inp))).
  pose proof Hsp as (S1 & S2 & S3). repeat split; try assumption; lia.
Qed.

Lemma layout_facts : ltac2:(tb__ "0|4|
S10S31S3S2cS2dVsp;Vdraw;Vinp;R1A7S14Q40M0S11R2P1A2A2S13S14G0S11R3P6A2A2S13S0S0S4Z7fff80000000R2A2S4R2S8Z2Z2fA2M1A2A2S0S1S13S7R2Z10M2A2Z0A3S0S4S5R2Z50A2R1A2S0S4S5R1G2A2M3G1A2S0S4G3S5R2Z2228cfA2A2S0S4R2S14G0S11R4P4A2A2A2S0S4R2R1A2S1S13R2S14G0Vsp;A2A3A2A2A2A2A2A2A2Tr6;Tx;F_;Frho;").
Proof.
  clear - Hent Hinp. intros rho HJr. destruct Hent as (Hsp & _ & _ & Hfit).
  pose proof (nums sp inp Hsp Hinp) as N. cbv zeta in N.
  destruct N as (Nsp & N16 & Nargc & Nenvc & Nstr & _ & _ & Nrnd & Npad & Ntab1 & Ntab2 & Nlen & _ & _).
  pose proof (LEN_fit sp inp Hinp Hfit) as LF. rewrite sp_hi_val in LF.
  rewrite (ji_sp _ _ _ _ _ _ _ HJr), (ji_rand _ _ _ _ _ _ _ HJr), (ji_argv0 _ _ _ _ _ _ _ HJr). cbv zeta.
  pose proof (total_arg_bytes_nonneg (in_argv inp)). pose proof (total_arg_bytes_nonneg (in_envp inp)).
  pose proof (Zle_0_nat (tab (in_argv inp))). pose proof (Zle_0_nat (tab (in_envp inp))). pose proof (Zle_0_nat (pad_len (in_argv inp) (in_envp inp))).
  rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite !(Z.mod_small (bv_unsigned sp + _) (2 ^ 64)) by lia.
  repeat split; lia.
Qed.

Lemma arg_layout_of_Jinit : ltac2:(tb__ "0|0|
S10S31S3S2cS2dVsp;Vdraw;Vinp;R1A7S3fR2A1F_;Frho;").
Proof.
  clear - Hent Hinp. intros rho HJr. destruct Hent as (Hsp & _ & _ & Hfit).
  pose proof (nums sp inp Hsp Hinp) as N. cbv zeta in N.
  destruct N as (Nsp & N16 & Nargc & Nenvc & Nstr & _ & Nlen0 & Nrnd & Npad & Ntab1 & Ntab2 & Nlen & _ & _).
  pose proof (LEN_fit sp inp Hinp Hfit) as LF. rewrite sp_hi_val in LF.
  unfold arg_layout.
  rewrite (ji_sp _ _ _ _ _ _ _ HJr), (ji_argc _ _ _ _ _ _ _ HJr), (ji_envc _ _ _ _ _ _ _ HJr), (ji_argv0 _ _ _ _ _ _ _ HJr), (ji_len0 _ _ _ _ _ _ _ HJr).
  pose proof (Zle_0_nat (tab (in_argv inp))). pose proof (Zle_0_nat (tab (in_envp inp))). pose proof (Zle_0_nat (pad_len (in_argv inp) (in_envp inp))).
  rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite !Z.mod_small by lia. repeat split; lia.
Qed.

Lemma Jinit_agree : ltac2:(tb__ "0|0|
S10S10S31S3S2cS2dVsp;Vdraw;Vinp;R2A7S12P14R3R2A3S31S3S2cS2dVsp;Vdraw;Vinp;R3A7F_;F_;Frho';Frho;").
Proof.
  clear. intros rho rho' HJr (Hw & Hl & Hm). destruct HJr; constructor; try (rewrite <- Hw by (cbv; reflexivity); assumption); try (rewrite <- Hl; assumption).
  intros a. rewrite <- Hm. auto.
Qed.

Definition QMain : assn := ltac2:(tb__ "0|3|
S44S2S15Q40M0A1M1G1S2S10S10S0S0S6Z0S14G0R2A2M2A2S6G2S3eA2A2S0S31S3S2cS2dVsp;Vdraw;Vinp;R1A7S41S34R2A1S40R1R3A4A2A2Lrho;A2Ltid;A2Lw;").

Theorem start_main_A : ltac2:(tb__ "0|0|
S43S3Vok;S36S3S32Vm0;A1S2eVrhoI;A4S35A4").
Proof.

  eapply triple_seq; [exact (start0_sum_A sp brk mb draw lim inp Hent Hinp rhoI HJ ok (OKF _ K0_nil) (OKP _ K0_nil) (OKF _ K1_nil))|].
  apply triple_ex; intros L. apply triple_ex; intros rho1. apply triple_pure; intros [<-|[]]. apply triple_pure; intros Hag1. cbn [lf_state].
  eapply triple_conseq with (P := fun w => exists tid, 0 < bv_unsigned tid < PID_MAX_ENVELOPE /\ SP segsA (Kx (M1 tid)) S_ctor rho1 w); [| intros w Hw; exact Hw |].
  { intros w [Hsm [Htr (tid & Htid & Hmd)]]. exists tid. split; [exact Htid|]. split; [exact Hsm|]. split; [exact Htr | exact Hmd]. }
  apply triple_ex; intros tid. apply triple_pure; intros Htid.
  pose proof (Jinit_agree rhoI rho1 HJ Hag1) as HJ1.
  pose proof (M1_fields tid) as (Fh & Flz & Fmt & Fres & Fmaps & Fna & Flim & Fsb & Fbrk & Fisp & Fused & _).
  pose proof brk_facts as [Hbrk Hbal]. pose proof sp_facts as (Hwin & Hspr & Hsp16).
  pose proof (layout_facts rho1 HJ1) as LF. cbv zeta in LF. destruct LF as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8).
  assert (Htop : init_sp_ok (m_vmmaps (M1 tid))) by (unfold init_sp_ok; rewrite Fisp; exact Hwin).
  eapply triple_conseq; [intros w Hw; exact Hw | |].
  2:{ apply (startA_main (M1 tid) B0 Fh Flz Fmt Fres Fmaps Fna ltac:(rewrite Fused; unfold B0; lia) ltac:(rewrite Flim; unfold B0; lia) Htop
               ltac:(rewrite Fsb, Fbrk; reflexivity) ltac:(rewrite Fbrk; exact Hbrk) ltac:(rewrite Fbrk; exact Hbal) ok (OKF _ (Kx_nil _)) OKFA OKPA rho1).
      - rewrite Fisp. exact X8.
      - exact X6.
      - exact X7.
      - exact X1.
      - exact X2.
      - exact X3.
      - exact X4.
      - exact X5.
      - exact (arg_layout_of_Jinit rho1 HJ1). }
  intros w Hw. exists tid, rho1. split; [exact Htid|]. split; [exact HJ1 | exact Hw].
Qed.

Theorem start_main_ex_A : ltac2:(tb__ "0|0|
S42S3S36S3S32Vm0;A1S2eVrhoI;A4S35A3").
Proof.
  eapply etriple_seq; [exact (start0_sum_ex_A sp brk mb draw lim inp Hent Hinp rhoI HJ)|].
  apply etriple_ex; intros L. apply etriple_ex; intros rho1. apply etriple_pure; intros [<-|[]]. apply etriple_pure; intros Hag1. cbn [lf_state].
  eapply etriple_conseq with (P := fun w => exists tid, 0 < bv_unsigned tid < PID_MAX_ENVELOPE /\ SP segsA (Kx (M1 tid)) S_ctor rho1 w); [| intros w Hw; exact Hw |].
  { intros w [Hsm [Htr (tid & Htid & Hmd)]]. exists tid. split; [exact Htid|]. split; [exact Hsm|]. split; [exact Htr | exact Hmd]. }
  apply etriple_ex; intros tid. apply etriple_pure; intros Htid.
  pose proof (Jinit_agree rhoI rho1 HJ Hag1) as HJ1.
  pose proof (M1_fields tid) as (Fh & Flz & Fmt & Fres & Fmaps & Fna & Flim & Fsb & Fbrk & Fisp & Fused & _).
  pose proof brk_facts as [Hbrk Hbal]. pose proof sp_facts as (Hwin & Hspr & Hsp16).
  pose proof (layout_facts rho1 HJ1) as LF. cbv zeta in LF. destruct LF as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8).
  assert (Htop : init_sp_ok (m_vmmaps (M1 tid))) by (unfold init_sp_ok; rewrite Fisp; exact Hwin).
  eapply etriple_conseq; [intros w Hw; exact Hw | |].
  2:{ apply (startA_main_ex (M1 tid) B0 Flz Fmt Fres Fmaps Fna ltac:(rewrite Fused; unfold B0; lia) ltac:(rewrite Flim; unfold B0; lia) Htop
               ltac:(rewrite Fsb, Fbrk; reflexivity) ltac:(rewrite Fbrk; exact Hbrk) ltac:(rewrite Fbrk; exact Hbal) ok OKFA OKPA rho1).
      - rewrite Fisp. exact X8.
      - exact X6.
      - exact X7.
      - exact X1.
      - exact X2.
      - exact X3.
      - exact X4.
      - exact X5.
      - exact (arg_layout_of_Jinit rho1 HJ1). }
  intros w Hw. exists tid, rho1. split; [exact Htid|]. split; [exact HJ1 | exact Hw].
Qed.

End Main.
