(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import PrimInt63 Uint63.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Cells Frame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require ALib.Mem ALib.Step.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AMalloc_iface AInstanceM AInstanceU AMalloc_iface2 AInstanceU2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require MainEntry.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs StepSoundBase StepSound PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import Nodes CertSound Ops CtrSys DrvShape DrvRoot DrvLib LibLib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require RunConst InitMem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require RootAsan2 RootAsanN AsanRun AsanImgx AsanDrun AsanAcct AcctPlug.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Acct AcctRoot.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require ARepAtMain ATsafeOps.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Ops ClientX TdOps TdInst.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.AsanU Require UnivAsan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2F Require T_Asan2F.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2L Require T_Asan2L.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2E Require T_Asan2E.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2A Require T_Asan2A.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2T Require T_Asan2T.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.AsanNU Require T_AsanNU.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2D Require T_Asan2D.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.LibRun Require Asan_r12.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueAsm.Run Require RunAsanF RunAsanATND TopAsanF TopAsanATND.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueAsm.Run Require Registry_Asan2F Registry_Asan2L Registry_Asan2E Registry_Asan2A Registry_Asan2T Registry_AsanNU Registry_Asan2D.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require AsanPB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.W2 Require ExhFirst.
Import ListNotations.
Import W64 Val FI St Step Plan ValP StepB StepS PlanS FXN CertS DrvLib LibLib HeapOp DrvShape.
Local Notation AIu2 := (AInstanceU2.AIu2 ExhFirst.exh_first).
Open Scope Z_scope.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module ME := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.MainEntry.
Module R2 := RootAsan2.RootAsan2.
Module RN := RootAsanN.RootAsanN.
Module OUR := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAlg.
Module RCo := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.RunConst.

Section MainAsan.

Let ACCT (rc : runConstT) : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop := @Acct.ACCT rc AsanAcct.NMAX AsanAcct.SHFIX.
Let COVP (rc : runConstT) : Model -> word -> Prop := Acct.COVPb AsanAcct.SHFIX.
Let NMAX : nat := AsanAcct.NMAX.
Let ACCT_led (rc : runConstT) := @AcctPlug.ACCT_ledx rc.
Let ACCT_cov (rc : runConstT) := @AcctPlug.ACCT_covx rc.
Let ACCT_cov_sh (rc : runConstT) := @AcctPlug.ACCT_cov_shx rc.
Let ACCT_mat (rc : runConstT) := @AcctPlug.ACCT_matx rc.
Let AI_frame_top (rc : runConstT) := @AcctPlug.AI_frame_topx rc.
Let ACCT_fds (rc : runConstT) := @AcctPlug.ACCT_fdsx rc.
Definition Cw {rc : runConstT} : client_world := Ops.UO.unp_cw asegs (ClientX.CX.XTP asegs).

Definition RAx (rc : runConstT) (en : ExecEntry) (inp : ProcInput) (Hva : valid_argv (in_argv inp)) : drun :=
  AsanDrun.RA AsanImgx.IMGX_A AsanImgx.IMGX_A_ok (ACCT rc) (COVP rc) NMAX (ACCT_led rc) (ACCT_cov rc) (ACCT_cov_sh rc) (ACCT_mat rc) UnivAsan.UNIV (AI_frame_top rc) Cw (ACCT_fds rc)
              AsanImgx.IMGX_A_rs3 inp (en_sp en) (en_draw en) Hva.

Definition G0_stmt : Prop := forall rc en inp Hva (Hsp : valid_sp (en_sp en)) (Hfit : entry_stack_fits (en_sp en) (in_argv inp) (in_envp inp)) E0 K,
  r_PB (RAx rc en inp Hva) (Val.eb E0) ->
  LNODE asegs (RAx rc en inp Hva) Asan_r12.LibRunAsan_r12.N E0 K (t_st T_Asan2F.R_LIBGEN_r12_RET) ->
  LNODE asegs (RAx rc en inp Hva) Asan_r12.LibRunAsan_r12.N E0 K (t_st T_Asan2L.T_G0_r31o5n0o1n63o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0).
Hypothesis G0 : G0_stmt.

Lemma UNIV_ok : ARepAtMain.univ_ok UnivAsan.UNIV.
Proof. split; [apply Nat.leb_le; vm_compute; reflexivity| vm_compute; discriminate]. Qed.
Lemma CRED0_le : bv_unsigned (wbv (wlit RunAsanF.CRED0i)) <= ATsafeOps.CRED0.
Proof. vm_compute. discriminate. Qed.
Lemma H0X : forall (rc : runConstT) en inp ms mo, ME.amain_at en inp ms mo -> bv_unsigned (en_sp en) = ATOP + 8388608 ->
  exists (L : alayout) (RNG : footprint) (sta : astate),
    AHEAP AIu2 L RNG sta [] (ms_mem ms) /\ ACCT rc (wbv (wlit RunAsanF.CRED0i)) L RNG sta [] mo /\ incl UnivAsan.UNIV (al_U L) /\ lazy_shape C0 mo /\ aprist sta.
Proof.
  intros rc en inp ms mo HM USP.
  destruct (AcctRoot.h0_at_main UnivAsan.UNIV AsanAcct.SHFIX AsanAcct.KSH AsanAcct.NMAX en inp ms mo (wbv (wlit RunAsanF.CRED0i))
              UNIV_ok AsanAcct.SHFIX_fin AsanAcct.KSH0
              ltac:(rewrite AsanAcct.NMAX_Z; unfold AsanAcct.KSH; lia)
              HM USP CRED0_le) as (L & RNG & sta & AH & AC & HU & LZ & APR).
  exists L, RNG, sta. split; [exact AH|]. split; [exact AC|]. split; [exact HU|]. split; [| exact APR].
  intros z Hz. apply LZ. unfold C0, W64.two64 in Hz. change (2 ^ 64) with 18446744073709551616. exact Hz.
Qed.

Lemma fam_absent : forall inp, valid_argv (in_argv inp) -> (length (AsanDrun.p1 inp) < 4096)%nat ->
  (AsanDrun.p1 inp = [] \/ (path_is_dirref (AsanDrun.p1 inp) = false /\ fs_lookup (in_fs inp) (AsanDrun.p1 inp) = None)) ->
  path_has_slash (AsanDrun.p1 inp) = false /\ path_is_dirref (AsanDrun.p1 inp) = false /\ (length (AsanDrun.p1 inp) < 4096)%nat /\
  (AsanDrun.p1 inp = [] \/ forall model, AsanDrun.MP inp model -> fs_lookup (m_fs model) (AsanDrun.p1 inp) = None).
Proof.
  intros inp Hva Hs Hc.
  assert (NS : path_has_slash (AsanDrun.p1 inp) = false).
  { pose proof Hva as (_ & _ & _ & _ & HSL). unfold AsanDrun.p1. clear - HSL. destruct (in_argv inp) as [|x [|y l]]; cbn [hd tl]; try reflexivity.
    exact (proj1 (proj1 (Forall_forall _ _) HSL y (or_introl eq_refl))). }
  split; [exact NS|]. split.
  { destruct Hc as [E|[D _]]; [rewrite E; reflexivity| exact D]. }
  split; [exact Hs|].
  destruct Hc as [E|[_ L]]; [left; exact E| right]. intros model HMP. unfold AsanDrun.MP, AsanDrun.fs0 in HMP. rewrite HMP. exact L.
Qed.

Lemma CRED0_same : RunAsanATND.CRED0i = RunAsanF.CRED0i.
Proof. reflexivity. Qed.
Lemma opt_cases {A} (o : option A) : (exists a, o = Some a) \/ o = None.
Proof. destruct o as [a|]; [left; exists a; reflexivity| right; reflexivity]. Qed.

Theorem MAIN : forall en inp, valid_entry (mkImage asegs a_init_pc a_phdrs) en inp -> valid_input_either inp ->
  forall ms mo, ME.amain_at en inp ms mo -> OUR.realizes asegs (mkCfg ms mo) (K inp).
Proof.
  intros en inp Hen Hi ms mo HM.
  pose proof Hi as (Hva & Hve & _ & _ & _ & _ & _ & Hhw & Hsz & _).
  apply (proj1 (valid_entry_sv48 _ en inp Hsz)) in Hen. destruct en as [sp brk0 mb rnd]. destruct Hen as (Hsp & _ & _ & Hfit).
  set (en := mkEntry sp brk0 mb rnd) in *.
  set (rc := RCo.run_consts_of en (Z_to_bv 64 0) Hsp).
  assert (USP : bv_unsigned (en_sp en) = @ATOP rc + 8388608).
  { unfold rc. rewrite RCo.run_consts_of_ATOP. unfold InitMem.entry_atop, stack_max_size. cbn [en_sp en]. lia. }
  destruct (H0X rc en inp ms mo HM USP) as (L & RNG & sta & AH & AC & HU & LZ & APR).
  assert (H2 : TopAsanATND.H0_at (ACCT rc) en inp ms mo L RNG sta R2.PRIV).
  { split; [exact HM|]. split; [exact USP|]. split; [exact AH|]. split; [rewrite CRED0_same; exact AC|].
    split; [exact HU|]. split; [exact LZ|]. exact APR. }
  assert (HN : TopAsanATND.H0_at (ACCT rc) en inp ms mo L RNG sta RN.PRIV).
  { split; [exact HM|]. split; [exact USP|]. split; [exact AH|]. split; [rewrite CRED0_same; exact AC|].
    split; [exact HU|]. split; [exact LZ|]. exact APR. }

  pose proof (@Registry_Asan2L.ctab_Asan2L rc inp sp rnd Hva Hsp Hfit) as cL.
  pose proof (@Registry_Asan2E.ctab_Asan2E rc inp sp rnd Hva Hsp Hfit) as cE.
  pose proof (fun Hs Hc => @Registry_Asan2A.ctab_Asan2A rc inp sp rnd Hva Hsp Hfit (fam_absent inp Hva Hs Hc)) as cA.
  pose proof (fun Hl : (4096 <= length (AsanDrun.p1 inp))%nat => @Registry_Asan2T.ctab_Asan2T rc inp sp rnd Hva Hsp Hfit Hl) as cT.
  pose proof (@Registry_AsanNU.ctab_AsanNU rc inp sp rnd Hva Hsp Hfit) as cN.
  pose proof (@Registry_Asan2D.ctab_Asan2D rc inp sp rnd Hva Hsp Hfit) as cD.
  set (FAMA := @TopAsanATND.rz_absent_asan_top rc (ACCT rc) (COVP rc) NMAX (ACCT_led rc) (ACCT_cov rc) (ACCT_cov_sh rc) (ACCT_mat rc) (AI_frame_top rc) (ACCT_fds rc)
                en inp Hva Hve Hsp Hfit Hhw ms mo L RNG sta).
  set (FAMT := @TopAsanATND.rz_toolong_asan_top rc (ACCT rc) (COVP rc) NMAX (ACCT_led rc) (ACCT_cov rc) (ACCT_cov_sh rc) (ACCT_mat rc) (AI_frame_top rc) (ACCT_fds rc)
                en inp Hva Hve Hsp Hfit Hhw ms mo L RNG sta).
  set (FAMD := @TopAsanATND.rz_dir_asan_top rc (ACCT rc) (COVP rc) NMAX (ACCT_led rc) (ACCT_cov rc) (ACCT_cov_sh rc) (ACCT_mat rc) (AI_frame_top rc) (ACCT_fds rc)
                en inp Hva Hve Hsp Hfit Hhw ms mo L RNG sta).
  set (FAMN := @TopAsanATND.rz_usage_asan_top rc (ACCT rc) (COVP rc) NMAX (ACCT_led rc) (ACCT_cov rc) (ACCT_cov_sh rc) (ACCT_mat rc) (AI_frame_top rc) (ACCT_fds rc)
                en inp Hva Hve Hsp Hfit Hhw ms mo L RNG sta).
  set (FAMF := @TopAsanF.rz_file_asan_top rc (ACCT rc) (COVP rc) NMAX (ACCT_led rc) (ACCT_cov rc) (ACCT_cov_sh rc) (ACCT_mat rc) (AI_frame_top rc) (ACCT_fds rc)
                en inp Hva Hve Hsp Hfit Hhw).

  destruct (Nat.eq_dec (length (in_argv inp)) 2) as [Hargc2 | HargcN]; [| exact (FAMN HargcN cN HN)].
  destruct (Nat.lt_ge_cases (length (AsanDrun.p1 inp)) 4096) as [Hs | Hl]; [| exact (FAMT Hargc2 Hl (cT Hl) H2)].
  destruct (list_eq_dec (@bv_eq_dec 8) (AsanDrun.p1 inp) []) as [Hnil | Hne]; [exact (FAMA Hargc2 Hs (or_introl Hnil) (cA Hs (or_introl Hnil)) H2)|].
  destruct (Sumbool.sumbool_of_bool (path_is_dirref (AsanDrun.p1 inp))) as [Hd | Hd]; [exact (FAMD Hargc2 Hd cD H2)|].
  destruct (opt_cases (fs_lookup (in_fs inp) (AsanDrun.p1 inp))) as [[f Hl] | Hl].
  - assert (Hfile : fs_lookup (in_fs inp) (AsanDrun.p1 inp) = Some (AsanDrun.file inp)) by (unfold AsanDrun.file, AsanDrun.fs0; rewrite Hl; reflexivity).
    assert (AC' : ACCT rc (wbv (wlit RunAsanF.CRED0i)) L RNG sta [] mo) by (rewrite <- CRED0_same; exact AC).
    assert (HFILE : fs_lookup (in_fs inp) (AsanDrun.p1 inp) <> None) by (rewrite Hfile; discriminate).
    pose proof (@Registry_Asan2F.ctab_Asan2F rc inp sp rnd Hva Hsp Hfit (AsanPB.MP_file inp HFILE)) as cF.
    exact (FAMF Hargc2 Hfile Hd Hne Hs cF cL cE (G0 rc en inp Hva Hsp Hfit) ms mo L RNG sta HM USP AH AC' HU LZ APR).
  - exact (FAMA Hargc2 Hs (or_intror (conj Hd Hl)) (cA Hs (or_intror (conj Hd Hl))) H2).
Qed.

End MainAsan.
