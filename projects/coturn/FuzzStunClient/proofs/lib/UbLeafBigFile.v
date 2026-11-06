(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Amb.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Spec TargetSpec TargetKDefs UbReadBase UbWorld UbTargetPre UbReadStage UbReadBig UbBigLeaves UbWorldK UbTargetPreK UbHeaderK SymPlanSoundA UbTargetTop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFast.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastS.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SumWalkFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.in_list ::= in_list_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.peel ::= peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SumWalkTac.rdn_peel1 ::= rdn_peel1_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Section BigFile.
  Context {AMB : Amb}.

Lemma ref_big_file : forall (sp0 p1 mb gm sec cn : word) (R : bvmap 5 word) (M : word -> option byte)
    (area brkv mas : Z) (VM : VmMaps) (path content : list byte) (stdin0 : InputStream) (fs0 : Fs) (tid : word),
  fs_lookup fs0 path = Some content -> (65536 <= Z.of_nat (length content))%Z ->
  area = (bv_unsigned mb + 4096)%Z ->
  read_pre sp0 p1 mb gm sec cn R M ->
  world0 area (bv_unsigned gm) brkv mas (bv_unsigned tid) M ->
  main_frame (bv_unsigned sp0) M ->
  vm_pre VM sp0 mb gm ->
  realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x13b14) M (seg_rom RSEGS))
                          (model_pre path VM stdin0 fs0 tid))
             (t_alt2 (t_die msg_oom fs0) (t_body content fs0)).
Proof.
  intros sp0 p1 mb gm sec cn R M area brkv mas VM path content stdin0 fs0 tid Hfile HL Harea RP W MF VP.
  set (L := Z.of_nat (length content)) in *.
  assert (Hvsp : valid_sp sp0).
  { pose proof (rp_sp0 _ _ _ _ _ _ _ _ RP) as Hs. unfold valid_sp, sp_window_lo, sp_window_hi. lia. }
  assert (Hpage0 : forall i, (0 <= i < 0x1000)%Z -> M (Z_to_bv 64 i) = None).
  { pose proof (w_img _ _ _ _ _ _ W) as Wi. apply (proj1 (Forall_forall _ _) Wi (0%Z, 0x1000%Z)). cbn. left. reflexivity. }
  (* [comment removed for export] *)
  apply (rz_conseq RSEGS _ (t_alt2 (t_die msg_oom fs0) (if (L <? 67108864)%Z then t_body content fs0 else t_die msg_refused fs0))).
  2:{ destruct (Z.ltb_spec0 L 67108864) as [Hs|Hb]; [apply t_eq_refl|].
      unfold t_body, MAX_INPUT. subst L. rewrite (proj2 (Z.leb_le _ _)) by lia. apply t_eq_refl. }
  change (model_pre path VM stdin0 fs0 tid) with (UbReadStage.modelG path stdin0 fs0 tid 0 VM).
  apply (read_big sp0 p1 mb gm sec cn path content stdin0 fs0 tid Hfile R M VM
           (t_body content fs0) (t_die msg_oom fs0) (t_die msg_refused fs0) RP VP Hpage0 HL).
  - (* [comment removed for export] *)
    apply (big_oom_branch sp0 gm area brkv mas tid M path stdin0 fs0 Hvsp W).
  - (* [comment removed for export] *)
    apply (big_refused_leaf sp0 gm area brkv mas tid M path stdin0 fs0 Hvsp W).
  - (* [comment removed for export] *)
    intros k Hk Hrange. unfold post_cont. intros R' M' V' B e RQ.
    apply (header_phase_k k sp0 p1 mb gm sec cn B e tid area brkv mas content M R' M' V' stdin0 fs0 Hk Hvsp RQ W MF).
    + unfold capk. subst L. exact Hrange.
    + intros R'' M'' TPK TVK.
      pose proof (target_phase_k_top k Hk (bv_unsigned sp0) (bv_unsigned B) area brkv mas (bv_unsigned tid) content
                    R'' M'' V' (model_post V' stdin0 fs0 tid) TPK TVK (SPSA.std_model_mk _ _ _ _ _)) as X.
      exact X.
Qed.
End BigFile.
