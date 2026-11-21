(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the section hypotheses entry_launch_ok_va Sv48 and valid_launch in place of entry_stack_fits, passed to aroot2_st_ok; rz_file_asan also gives the run predicate's far-end channel reader, from the main entry's am_reader; the file family's certificates per CONFIG_RSEQ value, chosen by the run's own value, each one's first template the root at its region 3, the ASan images' auxv with AT_PHNUM's value 11). *)
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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require RootAsan2 InitAsan2 AsanRun AsanRoot AsanRootAsm AsanDrun AsanPB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Auxv.
(* The CONFIG_RSEQ copies first: their short names are shadowed by the in-place ones below, and are used only
   through the full-path aliases after the imports. *)
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2FR Require T_Asan2F.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.RunR Require Asan2F_1 Asan2F_7.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2F Require T_Asan2F.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run Require Asan2F_1 Asan2F_7.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.W2 Require ExhFirst.
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
Module OUR := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAlg.
Module TFR := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2FR.T_Asan2F.
Module H1R := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.RunR.Asan2F_1.
Module N7R := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.RunR.Asan2F_7.

Section RunAsanF.
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
Hypothesis Hlau : entry_launch_ok_va Sv48 en inp.
Hypothesis Hhw : valid_hwcap (in_hwcap inp).
Hypothesis Hvl : valid_launch inp.
Hypothesis Hargc2 : length (in_argv inp) = 2%nat.

Let p1 := AsanDrun.p1 inp.
Let file := AsanDrun.file inp.
Lemma argv_eq : in_argv inp = [AsanDrun.a0 inp; AsanDrun.p1 inp].
Proof. clear - Hargc2. unfold AsanDrun.a0, AsanDrun.p1. destruct (in_argv inp) as [|a [|b [|c l]]]; try discriminate Hargc2. reflexivity. Qed.
Let RA : drun := AsanDrun.RA IMGX IMGX_aci ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw ACCT_fds IMGX_rs3 inp (en_sp en) (en_draw en) Hva.
Let OPSA : optable := AsanRun.OPSA IMGX IMGX_aci ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file.
Definition CRED0i : int := 51539607552%uint63.

Hypothesis HYPS : Asan2F_1.hyps RA.
(* the same family's certificates for the start state with CONFIG_RSEQ *)
Hypothesis HYPSR : H1R.hyps RA.

(* each certificate's first template is the root at its region 3: the auxv without CONFIG_RSEQ in place, with it
   in the copy *)
Lemma ROOT_EQ : T_Asan2F.T_DRV2 = I2.ROOT_with (Auxv.Auxv.R3Tb_asan false) (AsanRootAsm.ROOT_OPS CRED0i).
Proof. apply StEqb.st_eqb_eq. vm_compute. reflexivity. Qed.
Lemma ROOT_EQ_R : TFR.T_DRV2 = I2.ROOT_with (Auxv.Auxv.R3Tb_asan true) (AsanRootAsm.ROOT_OPS CRED0i).
Proof. apply StEqb.st_eqb_eq. vm_compute. reflexivity. Qed.

Hypothesis Hfile : fs_lookup (in_fs inp) p1 = Some file.
Hypothesis Hndir : path_is_dirref p1 = false.
Hypothesis Hne : p1 <> [].
Hypothesis Hshort : (length p1 < 4096)%nat.

Lemma K_file : K inp = DR RA (FILE file).
Proof.
  unfold K. rewrite argv_eq. unfold DR, K2. cbn [r_fs r_a0 r_p1 RA AsanDrun.RA].
  replace (4096 <=? Z.of_nat (length p1)) with false by (symmetry; apply Z.leb_gt; lia).
  replace (path_eqb p1 []) with false by (destruct p1; [exfalso; apply Hne; reflexivity | reflexivity]).
  rewrite Hndir. unfold AsanDrun.fs0. rewrite Hfile. reflexivity.
Qed.

Theorem rz_file_asan : forall ms mo (L : alayout) (RNG : footprint) (sta : astate),
  ME.amain_at en inp ms mo ->
  bv_unsigned (en_sp en) = ATOP + 8388608 ->
  AHEAP AIu2 L RNG sta [] (ms_mem ms) -> ACCT (wbv (wlit CRED0i)) L RNG sta [] mo -> incl UNIV (al_U L) -> lazy_shape C0 mo -> aprist sta ->
  (forall ws, Forall (fun w => w_kind w = K_STACK) ws -> cw_holds Cw 0 [] [] ws (ms_mem ms)) ->
  (forall a, (exists seg, find_segment asegs a 1 = Some seg) -> ~ in_ivs IMGX a -> in_priv R2.PRIV a) ->
  OUR.realizes asegs (mkCfg ms mo) (K inp).
Proof.
  intros ms mo L RNG sta HM USP AH AC HU LZ APR CW0 IMGAP.
  assert (HMP : r_MP RA mo).
  { cbn [r_MP RA AsanDrun.RA]. unfold AsanDrun.MP, AsanDrun.fs0.
    destruct HM as (w0 & V0 & m0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & AMO). exact (conj (ME.am_fs _ _ _ _ AMO) (ME.am_reader _ _ _ _ AMO)). }
  rewrite K_file.
  (* the run's CONFIG_RSEQ value chooses the certificates: the copies with it, the in-place ones without *)
  destruct (la_rseq (SI.LA (en_sp en) (en_mmap_base en) inp)) eqn:HR.
  - destruct (AsanRootAsm.aroot2_st_ok IMGX IMGX_aci ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file IMGX_stksh
                (AsanDrun.xb inp) en inp ms mo CRED0i L RNG sta (Auxv.Auxv.R3Tb_asan true) Hva Hve Hsp Hlau Hhw Hvl Hargc2 HM
                (or_introl (f_equal Auxv.Auxv.R3Tb_asan (eq_sym HR))) USP AH AC HU LZ APR CW0 IMGAP) as (E & HE & HS).
    rewrite <- ROOT_EQ_R in HS.
    apply (N7R.N_T_DRV2 RA HYPSR E ms mo); [exact HE | exact HMP | exact HS].
  - destruct (AsanRootAsm.aroot2_st_ok IMGX IMGX_aci ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file IMGX_stksh
                (AsanDrun.xb inp) en inp ms mo CRED0i L RNG sta (Auxv.Auxv.R3Tb_asan false) Hva Hve Hsp Hlau Hhw Hvl Hargc2 HM
                (or_introl (f_equal Auxv.Auxv.R3Tb_asan (eq_sym HR))) USP AH AC HU LZ APR CW0 IMGAP) as (E & HE & HS).
    rewrite <- ROOT_EQ in HS.
    apply (Asan2F_7.N_T_DRV2 RA HYPS E ms mo); [exact HE | exact HMP | exact HS].
Qed.
End RunAsanF.
