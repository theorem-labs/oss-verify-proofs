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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AProto ABase AMalloc_iface AInstanceM AInstanceU AMalloc_iface2 AInstanceU2. Import AProto.TwinB ABase.TwinB AMalloc_iface.TwinB AInstanceM.TwinB AInstanceU.TwinB AMalloc_iface2.TwinB AInstanceU2.TwinB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require MainEntryBoth.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs StepSoundBase StepSound PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import Nodes CertSound Ops CtrSys DrvShape DrvRoot DrvLib LibLib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Op. Import Ledger.TwinB Op.TwinB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require RunConst InitMem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require AsanRun AsanImgx AsanDrun AsanAcct AcctPlug.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require RootBoth2 RootBothN.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Acct AcctRoot.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require ARepAtMain ATsafeOps.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Ops ClientX TdOps TdInst.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.BothU Require UnivBoth.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Both2F Require T_Both2F.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Both2L Require T_Both2L.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Both2E Require T_Both2E.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Both2A Require T_Both2A.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Both2T Require T_Both2T.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.BothNU Require T_BothNU.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Both2D Require T_Both2D.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.LibRun Require Both_r12.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueAsmB.Run Require RunBothF RunBothATND TopBothF TopBothATND.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueAsmB.Run Require Registry_Both2F Registry_Both2L Registry_Both2E Registry_Both2A Registry_Both2T Registry_BothNU Registry_Both2D.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require AsanPB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.W2 Require ExhFirst.
Import ListNotations.
Import W64 Val FI St Step Plan ValP StepB StepS PlanS FXN CertS DrvLib LibLib HeapOp DrvShape.
Local Notation AIu2 := (AInstanceU2.TwinB.AIu2 ExhFirst.TwinB.exh_first).
Open Scope Z_scope.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module ME := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.MainEntryBoth.
Module R2 := RootBoth2.RootBoth2.
Module RN := RootBothN.RootBothN.
Module OUR := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAlg.
Module RCo := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.RunConst.

Section MainBoth.

Let ACCT (rc : runConstT) : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop := @Acct.TwinB.ACCT rc AsanAcct.TwinB.NMAX AsanAcct.TwinB.SHFIX.
Let COVP (rc : runConstT) : Model -> word -> Prop := Acct.TwinB.COVPb AsanAcct.TwinB.SHFIX.
Let NMAX : nat := AsanAcct.TwinB.NMAX.
Let ACCT_led (rc : runConstT) := @AcctPlug.TwinB.ACCT_ledx rc.
Let ACCT_cov (rc : runConstT) := @AcctPlug.TwinB.ACCT_covx rc.
Let ACCT_cov_sh (rc : runConstT) := @AcctPlug.TwinB.ACCT_cov_shx rc.
Let ACCT_mat (rc : runConstT) := @AcctPlug.TwinB.ACCT_matx rc.
Let AI_frame_top (rc : runConstT) := @AcctPlug.TwinB.AI_frame_topx rc.
Let ACCT_fds (rc : runConstT) := @AcctPlug.TwinB.ACCT_fdsx rc.
Definition Cw {rc : runConstT} : client_world := Ops.UO.unp_cw bsegs (ClientX.CX.XTP bsegs).

Definition RAx (rc : runConstT) (en : ExecEntry) (inp : ProcInput) (Hva : valid_argv (in_argv inp)) : drun :=
  AsanDrun.TwinB.RA AsanImgx.TwinB.IMGX_A AsanImgx.TwinB.IMGX_A_ok (ACCT rc) (COVP rc) NMAX (ACCT_led rc) (ACCT_cov rc) (ACCT_cov_sh rc) (ACCT_mat rc) UnivBoth.UNIV (AI_frame_top rc) Cw (ACCT_fds rc)
              AsanImgx.TwinB.IMGX_A_rs3 inp (en_sp en) (en_draw en) Hva.

Definition G0_stmt : Prop := forall rc en inp Hva (Hsp : valid_sp (en_sp en)) (Hfit : entry_stack_fits (en_sp en) (in_argv inp) (in_envp inp)) E0 K,
  r_PB (RAx rc en inp Hva) (Val.eb E0) ->
  LNODE bsegs (RAx rc en inp Hva) Both_r12.LibRunBoth_r12.N E0 K (t_st T_Both2F.R_LIBGEN_r12_RET) ->
  LNODE bsegs (RAx rc en inp Hva) Both_r12.LibRunBoth_r12.N E0 K (t_st T_Both2L.T_G0_r31o5n0o1n63o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0).
Hypothesis G0 : G0_stmt.

Lemma UNIV_ok : ARepAtMain.TwinB.univ_ok UnivBoth.UNIV.
Proof. split; [apply Nat.leb_le; vm_compute; reflexivity| vm_compute; discriminate]. Qed.
Lemma CRED0_le : bv_unsigned (wbv (wlit RunBothF.CRED0i)) <= ATsafeOps.TwinB.CRED0.
Proof. vm_compute. discriminate. Qed.
Lemma H0X : forall (rc : runConstT) en inp ms mo, ME.bmain_at en inp ms mo -> bv_unsigned (en_sp en) = ATOP + 8388608 ->
  exists (L : alayout) (RNG : footprint) (sta : astate),
    AHEAP AIu2 L RNG sta [] (ms_mem ms) /\ ACCT rc (wbv (wlit RunBothF.CRED0i)) L RNG sta [] mo /\ incl UnivBoth.UNIV (al_U L) /\ lazy_shape C0 mo /\ aprist sta.
Proof.
  intros rc en inp ms mo HM USP.
  destruct (AcctRoot.TwinB.h0_at_main UnivBoth.UNIV AsanAcct.TwinB.SHFIX AsanAcct.TwinB.KSH AsanAcct.TwinB.NMAX en inp ms mo (wbv (wlit RunBothF.CRED0i))
              UNIV_ok AsanAcct.TwinB.SHFIX_fin AsanAcct.TwinB.KSH0
              ltac:(rewrite AsanAcct.TwinB.NMAX_Z; unfold AsanAcct.TwinB.KSH; lia)
              HM USP CRED0_le) as (L & RNG & sta & AH & AC & HU & LZ & APR).
  exists L, RNG, sta. split; [exact AH|]. split; [exact AC|]. split; [exact HU|]. split; [| exact APR].
  intros z Hz. apply LZ. unfold C0, W64.two64 in Hz. change (2 ^ 64) with 18446744073709551616. exact Hz.
Qed.

Lemma fam_absent : forall inp, valid_argv (in_argv inp) -> (length (AsanDrun.TwinB.p1 inp) < 4096)%nat ->
  (AsanDrun.TwinB.p1 inp = [] \/ (path_is_dirref (AsanDrun.TwinB.p1 inp) = false /\ fs_lookup (in_fs inp) (AsanDrun.TwinB.p1 inp) = None)) ->
  path_has_slash (AsanDrun.TwinB.p1 inp) = false /\ path_is_dirref (AsanDrun.TwinB.p1 inp) = false /\ (length (AsanDrun.TwinB.p1 inp) < 4096)%nat /\
  (AsanDrun.TwinB.p1 inp = [] \/ forall model, AsanDrun.TwinB.MP inp model -> fs_lookup (m_fs model) (AsanDrun.TwinB.p1 inp) = None).
Proof.
  intros inp Hva Hs Hc.
  assert (NS : path_has_slash (AsanDrun.TwinB.p1 inp) = false).
  { pose proof Hva as (_ & _ & _ & _ & HSL). unfold AsanDrun.TwinB.p1. clear - HSL. destruct (in_argv inp) as [|x [|y l]]; cbn [hd tl]; try reflexivity.
    exact (proj1 (proj1 (Forall_forall _ _) HSL y (or_introl eq_refl))). }
  split; [exact NS|]. split.
  { destruct Hc as [E|[D _]]; [rewrite E; reflexivity| exact D]. }
  split; [exact Hs|].
  destruct Hc as [E|[_ L]]; [left; exact E| right]. intros model HMP. unfold AsanDrun.TwinB.MP, AsanDrun.TwinB.fs0 in HMP. rewrite HMP. exact L.
Qed.

Lemma CRED0_same : RunBothATND.CRED0i = RunBothF.CRED0i.
Proof. reflexivity. Qed.
Lemma opt_cases {A} (o : option A) : (exists a, o = Some a) \/ o = None.
Proof. destruct o as [a|]; [left; exists a; reflexivity| right; reflexivity]. Qed.

Theorem MAIN : forall en inp, valid_entry (mkImage bsegs b_init_pc b_phdrs) en inp -> valid_input_either inp ->
  forall ms mo, ME.bmain_at en inp ms mo -> OUR.realizes bsegs (mkCfg ms mo) (K inp).
Proof.
  intros en inp Hen Hi ms mo HM.
  pose proof Hi as (Hva & Hve & _ & _ & _ & _ & _ & Hhw & Hsz & _).
  apply (proj1 (valid_entry_sv48 _ en inp Hsz)) in Hen. destruct en as [sp brk0 mb rnd]. destruct Hen as (Hsp & _ & _ & Hfit).
  set (en := mkEntry sp brk0 mb rnd) in *.
  set (rc := RCo.run_consts_of en (Z_to_bv 64 0) Hsp).
  assert (USP : bv_unsigned (en_sp en) = @ATOP rc + 8388608).
  { unfold rc. rewrite RCo.run_consts_of_ATOP. unfold InitMem.entry_atop, stack_max_size. cbn [en_sp en]. lia. }
  destruct (H0X rc en inp ms mo HM USP) as (L & RNG & sta & AH & AC & HU & LZ & APR).
  assert (H2 : TopBothATND.H0_at (ACCT rc) en inp ms mo L RNG sta R2.PRIV).
  { split; [exact HM|]. split; [exact USP|]. split; [exact AH|]. split; [rewrite CRED0_same; exact AC|].
    split; [exact HU|]. split; [exact LZ|]. exact APR. }
  assert (HN : TopBothATND.H0_at (ACCT rc) en inp ms mo L RNG sta RN.PRIV).
  { split; [exact HM|]. split; [exact USP|]. split; [exact AH|]. split; [rewrite CRED0_same; exact AC|].
    split; [exact HU|]. split; [exact LZ|]. exact APR. }

  pose proof (@Registry_Both2L.ctab_Both2L rc inp sp rnd Hva Hsp Hfit) as cL.
  pose proof (@Registry_Both2E.ctab_Both2E rc inp sp rnd Hva Hsp Hfit) as cE.
  pose proof (fun Hs Hc => @Registry_Both2A.ctab_Both2A rc inp sp rnd Hva Hsp Hfit (fam_absent inp Hva Hs Hc)) as cA.
  pose proof (fun Hl : (4096 <= length (AsanDrun.TwinB.p1 inp))%nat => @Registry_Both2T.ctab_Both2T rc inp sp rnd Hva Hsp Hfit Hl) as cT.
  pose proof (@Registry_BothNU.ctab_BothNU rc inp sp rnd Hva Hsp Hfit) as cN.
  pose proof (@Registry_Both2D.ctab_Both2D rc inp sp rnd Hva Hsp Hfit) as cD.
  set (FAMA := @TopBothATND.rz_absent_asan_top rc (ACCT rc) (COVP rc) NMAX (ACCT_led rc) (ACCT_cov rc) (ACCT_cov_sh rc) (ACCT_mat rc) (AI_frame_top rc) (ACCT_fds rc)
                en inp Hva Hve Hsp Hfit Hhw ms mo L RNG sta).
  set (FAMT := @TopBothATND.rz_toolong_asan_top rc (ACCT rc) (COVP rc) NMAX (ACCT_led rc) (ACCT_cov rc) (ACCT_cov_sh rc) (ACCT_mat rc) (AI_frame_top rc) (ACCT_fds rc)
                en inp Hva Hve Hsp Hfit Hhw ms mo L RNG sta).
  set (FAMD := @TopBothATND.rz_dir_asan_top rc (ACCT rc) (COVP rc) NMAX (ACCT_led rc) (ACCT_cov rc) (ACCT_cov_sh rc) (ACCT_mat rc) (AI_frame_top rc) (ACCT_fds rc)
                en inp Hva Hve Hsp Hfit Hhw ms mo L RNG sta).
  set (FAMN := @TopBothATND.rz_usage_asan_top rc (ACCT rc) (COVP rc) NMAX (ACCT_led rc) (ACCT_cov rc) (ACCT_cov_sh rc) (ACCT_mat rc) (AI_frame_top rc) (ACCT_fds rc)
                en inp Hva Hve Hsp Hfit Hhw ms mo L RNG sta).
  set (FAMF := @TopBothF.rz_file_asan_top rc (ACCT rc) (COVP rc) NMAX (ACCT_led rc) (ACCT_cov rc) (ACCT_cov_sh rc) (ACCT_mat rc) (AI_frame_top rc) (ACCT_fds rc)
                en inp Hva Hve Hsp Hfit Hhw).

  destruct (Nat.eq_dec (length (in_argv inp)) 2) as [Hargc2 | HargcN]; [| exact (FAMN HargcN cN HN)].
  destruct (Nat.lt_ge_cases (length (AsanDrun.TwinB.p1 inp)) 4096) as [Hs | Hl]; [| exact (FAMT Hargc2 Hl (cT Hl) H2)].
  destruct (list_eq_dec (@bv_eq_dec 8) (AsanDrun.TwinB.p1 inp) []) as [Hnil | Hne]; [exact (FAMA Hargc2 Hs (or_introl Hnil) (cA Hs (or_introl Hnil)) H2)|].
  destruct (Sumbool.sumbool_of_bool (path_is_dirref (AsanDrun.TwinB.p1 inp))) as [Hd | Hd]; [exact (FAMD Hargc2 Hd cD H2)|].
  destruct (opt_cases (fs_lookup (in_fs inp) (AsanDrun.TwinB.p1 inp))) as [[f Hl] | Hl].
  - assert (Hfile : fs_lookup (in_fs inp) (AsanDrun.TwinB.p1 inp) = Some (AsanDrun.TwinB.file inp)) by (unfold AsanDrun.TwinB.file, AsanDrun.TwinB.fs0; rewrite Hl; reflexivity).
    assert (AC' : ACCT rc (wbv (wlit RunBothF.CRED0i)) L RNG sta [] mo) by (rewrite <- CRED0_same; exact AC).
    assert (HFILE : fs_lookup (in_fs inp) (AsanDrun.TwinB.p1 inp) <> None) by (rewrite Hfile; discriminate).
    pose proof (@Registry_Both2F.ctab_Both2F rc inp sp rnd Hva Hsp Hfit (AsanPB.TwinB.MP_file inp HFILE)) as cF.
    exact (FAMF Hargc2 Hfile Hd Hne Hs cF cL cE (G0 rc en inp Hva Hsp Hfit) ms mo L RNG sta HM USP AH AC' HU LZ APR).
  - exact (FAMA Hargc2 Hs (or_intror (conj Hd Hl)) (cA Hs (or_intror (conj Hd Hl))) H2).
Qed.

End MainBoth.
