(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Instr State Step Plan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import Ops StackInit InitLib DrvShape DrvLib StEqb.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require GlueA FakeLaw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require RootAsan2 InitAsan2 RootAsanN InitAsanN AsanRun AsanRoot AsanRootAsm AsanRootAsmN AsanDrun AsanPB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2A Require T_Asan2A.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2T Require T_Asan2T.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.AsanNU Require T_AsanNU.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2D Require T_Asan2D.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.W2 Require ExhFirst.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run Require Asan2A_1 Asan2A_5 Asan2T_1 Asan2T_5 AsanNU_1 AsanNU_6 Asan2D_1 Asan2D_10.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 St HeapOp DrvShape DrvLib.
Local Notation AIu2 := (AInstanceU2.AIu2 ExhFirst.exh_first).
Open Scope Z_scope.
Unset Lia Cache.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module ME := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.MainEntry.
Module I2 := InitAsan2.InitAsan2.
Module R2 := RootAsan2.RootAsan2.
Module IN := InitAsanN.InitAsanN.
Module RN := RootAsanN.RootAsanN.
Module OUR := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAlg.

Section RunAsanATN.
Context {rc : runConstT}.
Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AIu2 IMGX.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable COVP : Model -> word -> Prop.
Variable NMAX : nat.
Hypothesis ACCT_led : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo ->
  exists A : word -> Prop, ainv (m_vm_lazy mo) A NMAX mo /\ (forall p, COVP mo p -> A p).
Hypothesis ACCT_cov : forall aw L RNG st LBa m mo b z, ACCT aw L RNG st LBa mo -> AHEAP AIu2 L RNG st LBa m -> In b LBa ->
  (ab_addr b <= z < ab_addr b + ab_size b \/ shad (ab_addr b) <= z < shad (ab_addr b) + shlen (ab_size b + 7)) ->
  page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVP mo (page_base_of z).
Hypothesis ACCT_cov_sh : forall aw L RNG st LBa mo z, ACCT aw L RNG st LBa mo -> sh_cov z ->
  page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVP mo (page_base_of z).
Hypothesis ACCT_mat : forall aw L RNG st LBa mo mo', ACCT aw L RNG st LBa mo -> same_but_mat mo mo' ->
  List.NoDup (m_vm_materialized mo') ->
  (forall p, List.In p (m_vm_materialized mo') -> List.In p (m_vm_materialized mo) \/ COVP mo p) ->
  ACCT aw L RNG st LBa mo'.
Variable UNIV : list (list Z).
Hypothesis AI_frame_top : forall L RNG st LB m m',
  AHEAP AIu2 L RNG st LB m -> (forall a, 0 <= a < 2^47 -> m' (AM.wa a) = m (AM.wa a)) -> wmono asegs m m' -> AHEAP AIu2 L RNG st LB m'.
Variable Cw : client_world.
Hypothesis ACCT_fds : forall aw L RNG st LBa mo f, ACCT aw L RNG st LBa mo -> ACCT aw L RNG st LBa (with_fds f mo).
Hypothesis IMGX_rs3 : forall a, AsanRun.RS3 <= a < AsanRun.RS3 + 65536 -> in_ivs IMGX a.
Hypothesis IMGX_stksh : forall a', ATOP <= a' < 2 ^ 47 -> in_ivs IMGX (shad a').

Variables (en : ExecEntry) (inp : ProcInput).
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hsp : valid_sp (en_sp en).
Hypothesis Hfit : entry_stack_fits (en_sp en) (in_argv inp) (in_envp inp).
Hypothesis Hhw : valid_hwcap (in_hwcap inp).
Let p1 := AsanDrun.p1 inp.
Let file := AsanDrun.file inp.
Let RA : drun := AsanDrun.RA IMGX IMGX_aci ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw ACCT_fds IMGX_rs3 inp (en_sp en) (en_draw en) Hva.
Definition CRED0i : int := 51539607552%uint63.

Lemma ROOT_EQ_A : T_Asan2A.T_DRV2 = I2.ROOT_with (AsanRootAsm.ROOT_OPS CRED0i).
Proof. apply StEqb.st_eqb_eq. vm_compute. reflexivity. Qed.
Lemma ROOT_EQ_T : T_Asan2T.T_DRV2 = I2.ROOT_with (AsanRootAsm.ROOT_OPS CRED0i).
Proof. apply StEqb.st_eqb_eq. vm_compute. reflexivity. Qed.
Lemma ROOT_EQ_N : T_AsanNU.T_DRVN = IN.ROOT_with (AsanRootAsmN.ROOT_OPS CRED0i).
Proof. apply StEqb.st_eqb_eq. vm_compute. reflexivity. Qed.
Lemma ROOT_EQ_D : T_Asan2D.T_DRV2 = I2.ROOT_with (AsanRootAsm.ROOT_OPS CRED0i).
Proof. apply StEqb.st_eqb_eq. vm_compute. reflexivity. Qed.

Lemma argv_eq : length (in_argv inp) = 2%nat -> in_argv inp = [AsanDrun.a0 inp; AsanDrun.p1 inp].
Proof. intros H. clear - H. unfold AsanDrun.a0, AsanDrun.p1. destruct (in_argv inp) as [|a [|b [|c l]]]; try discriminate H. reflexivity. Qed.

Section H0.
Variables (ms : machine_state) (mo : Model) (L : alayout) (RNG : footprint) (sta : astate).
Hypothesis HM : ME.amain_at en inp ms mo.
Hypothesis USP : bv_unsigned (en_sp en) = ATOP + 8388608.
Hypothesis AH : AHEAP AIu2 L RNG sta [] (ms_mem ms).
Hypothesis AC : ACCT (wbv (wlit CRED0i)) L RNG sta [] mo.
Hypothesis HU : incl UNIV (al_U L).
Hypothesis LZ : lazy_shape C0 mo.
Hypothesis APR : aprist sta.
Hypothesis CW0 : forall ws, Forall (fun w => w_kind w = K_STACK) ws -> cw_holds Cw 0 [] [] ws (ms_mem ms).
Hypothesis IMGAP2 : forall a, (exists seg, find_segment asegs a 1 = Some seg) -> ~ in_ivs IMGX a -> in_priv R2.PRIV a.
Hypothesis IMGAPN : forall a, (exists seg, find_segment asegs a 1 = Some seg) -> ~ in_ivs IMGX a -> in_priv RN.PRIV a.

Lemma MP_ok : r_MP RA mo.
Proof. cbn [r_MP RA AsanDrun.RA]. unfold AsanDrun.MP, AsanDrun.fs0. destruct HM as (w0 & V0 & m0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & AMO). exact (ME.am_fs _ _ _ _ AMO). Qed.

Theorem rz_absent_asan : length (in_argv inp) = 2%nat -> (length p1 < 4096)%nat -> (p1 = [] \/ (path_is_dirref p1 = false /\ fs_lookup (in_fs inp) p1 = None)) ->
  Asan2A_1.hyps RA -> OUR.realizes asegs (mkCfg ms mo) (K inp).
Proof.
  intros Hargc2 Hshort Hcase HYPS.
  destruct (AsanRootAsm.aroot2_st_ok IMGX IMGX_aci ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file IMGX_stksh
              (AsanDrun.xb inp) en inp ms mo CRED0i L RNG sta Hva Hve Hsp Hfit Hhw Hargc2 HM USP AH AC HU LZ APR CW0 IMGAP2) as (E & HE & HS).
  assert (HK : K inp = DR RA OPENFAIL).
  { unfold K. rewrite (argv_eq Hargc2). unfold DR, K2. cbn [r_fs r_a0 r_p1 RA AsanDrun.RA]. fold p1.
    replace (4096 <=? Z.of_nat (length p1)) with false by (symmetry; apply Z.leb_gt; lia).
    destruct Hcase as [-> | [Hnd Hno]]; [reflexivity|].
    destruct (path_eqb p1 []); [reflexivity|]. rewrite Hnd. unfold AsanDrun.fs0. rewrite Hno. reflexivity. }
  rewrite HK. rewrite <- ROOT_EQ_A in HS.
  apply (Asan2A_5.N_T_DRV2 RA HYPS E ms mo); [exact HE| exact MP_ok| exact HS].
Qed.

Theorem rz_toolong_asan : length (in_argv inp) = 2%nat -> (4096 <= length p1)%nat -> Asan2T_1.hyps RA -> OUR.realizes asegs (mkCfg ms mo) (K inp).
Proof.
  intros Hargc2 Hlong HYPS.
  destruct (AsanRootAsm.aroot2_st_ok IMGX IMGX_aci ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file IMGX_stksh
              (AsanDrun.xb inp) en inp ms mo CRED0i L RNG sta Hva Hve Hsp Hfit Hhw Hargc2 HM USP AH AC HU LZ APR CW0 IMGAP2) as (E & HE & HS).
  assert (HK : K inp = DR RA OPENFAIL).
  { unfold K. rewrite (argv_eq Hargc2). unfold DR, K2. cbn [r_fs r_a0 r_p1 RA AsanDrun.RA]. fold p1.
    replace (4096 <=? Z.of_nat (length p1)) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
  rewrite HK. rewrite <- ROOT_EQ_T in HS.
  apply (Asan2T_5.N_T_DRV2 RA HYPS E ms mo); [exact HE| exact MP_ok| exact HS].
Qed.

Lemma p1_noslash : path_has_slash p1 = false.
Proof.
  pose proof Hva as (_ & _ & _ & _ & HSL). unfold p1, AsanDrun.p1. clear - HSL. destruct (in_argv inp) as [|x [|y l]]; cbn [hd tl]; try reflexivity.
  exact (proj1 (proj1 (Forall_forall _ _) HSL y (or_introl eq_refl))).
Qed.
Theorem rz_dir_asan : length (in_argv inp) = 2%nat -> path_is_dirref p1 = true -> Asan2D_1.hyps RA -> OUR.realizes asegs (mkCfg ms mo) (K inp).
Proof.
  intros Hargc2 Hdir HYPS.
  destruct (AsanRootAsm.aroot2_st_ok IMGX IMGX_aci ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file IMGX_stksh
              (AsanDrun.xb inp) en inp ms mo CRED0i L RNG sta Hva Hve Hsp Hfit Hhw Hargc2 HM USP AH AC HU LZ APR CW0 IMGAP2) as (E & HE & HS).
  assert (Hp : p1 = [Z_to_bv 8 46]).
  { pose proof Hva as (_ & _ & _ & _ & HSL). pose proof p1_noslash as NS. unfold path_is_dirref in Hdir. apply orb_prop in Hdir.
    destruct Hdir as [H1|H2]; [apply path_eqb_eq in H1; exact H1|].
    exfalso. apply path_eqb_eq in H2. unfold p1, AsanDrun.p1 in H2, NS. clear - HSL H2 Hargc2.
    destruct (in_argv inp) as [|x [|y l]]; cbn [hd tl] in H2; try discriminate Hargc2.
    pose proof (proj2 (proj1 (Forall_forall _ _) HSL y (or_introl eq_refl))) as ND. rewrite H2 in ND. cbn in ND. discriminate ND. }
  assert (HK : K inp = DR RA DIR).
  { unfold K. rewrite (argv_eq Hargc2). unfold DR, K2. cbn [r_fs r_a0 r_p1 RA AsanDrun.RA]. fold p1.
    replace (4096 <=? Z.of_nat (length p1)) with false by (rewrite Hp; reflexivity).
    replace (path_eqb p1 []) with false by (rewrite Hp; reflexivity).
    replace (path_is_dirref p1) with true by (rewrite Hp; reflexivity). reflexivity. }
  rewrite HK. rewrite <- ROOT_EQ_D in HS.
  apply (Asan2D_10.N_T_DRV2 RA HYPS E ms mo); [exact HE| exact MP_ok| exact HS].
Qed.

Theorem rz_usage_asan : length (in_argv inp) <> 2%nat -> AsanNU_1.hyps RA -> OUR.realizes asegs (mkCfg ms mo) (K inp).
Proof.
  intros HargcN HYPS.
  destruct (AsanRootAsmN.arootN_st_ok IMGX IMGX_aci ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file IMGX_stksh
              (AsanDrun.xb inp) en inp ms mo CRED0i L RNG sta Hva Hve Hsp Hfit Hhw HargcN HM USP AH AC HU LZ APR CW0 IMGAPN) as (E & HE & HS).
  assert (HK : K inp = DR RA USAGE).
  { unfold K, DR. cbn [r_fs r_a0 r_p1 RA AsanDrun.RA]. unfold AsanDrun.a0, AsanDrun.p1. pose proof HargcN as LN. set (l := in_argv inp) in LN |- *. clearbody l.
    destruct l as [|x [|y [|z l']]]; cbn [hd tl]; try reflexivity. exfalso. apply LN. reflexivity. }
  rewrite HK. rewrite <- ROOT_EQ_N in HS.
  apply (AsanNU_6.N_T_DRVN RA HYPS E ms mo); [exact HE| exact MP_ok| exact HS].
Qed.
End H0.
End RunAsanATN.
