(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Amb.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes ShapeLaws MmapSim AllocSim FileSim AgentLib MemSplit.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import SymExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymExec2 SymExec2Sound SymRun SymDrive SymDriveX.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import RefMemcpyLib RefNodes.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import LibKnowFrame LibKnowXfer RefReadLib UbReadBase UbReadStage UbReadChunk UbRead0 UbReadG0 UbReadG1 UbReadG2 UbReadG3 UbReadG4 UbReadG5 UbReadG6 UbReadG7 UbReadG8 UbReadG9 UbReadF1 UbReadF2 UbReadF3 UbReadF4 UbReadF5 UbReadF6 UbReadF7 UbReadF8 UbReadF9 UbReadF10.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFast.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SumWalkFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SumWalkTac.rdn_peel1 ::= rdn_peel1_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Big.
  Context {AMB : Amb}.
  Variables (sp0 p1 mb gm sec cn : word) (path content : list byte).
  Variables (stdin0 : InputStream) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (UbReadStage.modelG path stdin0 fs0 tid) (only parsing).

  (* [comment removed for export] *)
  Definition post_cont (k : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, read_post k sp0 p1 mb gm sec cn B e content M0 R M V ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x13bbc) M (seg_rom RSEGS)) (model_post V stdin0 fs0 tid)) K.

  Section Stages.
    Variables (M0 : word -> option byte) (K TOOM TREF : TSet).
    Hypothesis Hmb0 : (0x1000 <= bv_unsigned mb)%Z.
    Hypothesis Hmb1 : (bv_unsigned mb + 8192 <= bv_unsigned sp0 - 8388608)%Z.
    Hypothesis Hmba : (bv_unsigned mb mod 4096 = 0)%Z.
    Hypothesis HspR : (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z.
    Hypothesis HOOM : UbReadStage.oom_branch sp0 path stdin0 fs0 tid M0 TOOM.
    Hypothesis HREF : forall R' M' off V', oom_leaf sp0 M0 R' M' ->
      realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x13d08) M' (seg_rom RSEGS)) (modelG off V')) TREF.
    Hypothesis HPOST : forall k, (1 <= k <= 10)%Z -> (65536 * 2 ^ (k - 1) <= L < 65536 * 2 ^ k)%Z -> post_cont k M0 K.

    (* [comment removed for export] *)
    Definition SH10 : TSet := if (L <? 67108864)%Z then K else TREF.
    Definition SH9 : TSet := if (L <? 33554432)%Z then K else t_alt2 TOOM SH10.
    Definition SH8 : TSet := if (L <? 16777216)%Z then K else t_alt2 TOOM SH9.
    Definition SH7 : TSet := if (L <? 8388608)%Z then K else t_alt2 TOOM SH8.
    Definition SH6 : TSet := if (L <? 4194304)%Z then K else t_alt2 TOOM SH7.
    Definition SH5 : TSet := if (L <? 2097152)%Z then K else t_alt2 TOOM SH6.
    Definition SH4 : TSet := if (L <? 1048576)%Z then K else t_alt2 TOOM SH5.
    Definition SH3 : TSet := if (L <? 524288)%Z then K else t_alt2 TOOM SH4.
    Definition SH2 : TSet := if (L <? 262144)%Z then K else t_alt2 TOOM SH3.
    Definition SH1 : TSet := if (L <? 131072)%Z then K else t_alt2 TOOM SH2.


    Lemma HS10 : forall R M V B e, half 10 sp0 p1 mb gm sec cn B e content M0 R M V -> (33554432 <= L)%Z ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x13b8c) M (seg_rom RSEGS)) (modelG (held_of 10) V)) SH10.
    Proof.
      intros R M V B e ST HGE. unfold SH10. change (held_of 10) with 33554432%Z.
      destruct (Z.ltb_spec L 67108864) as [HLT|HGE2].
      - (* [comment removed for export] *)
        apply (UbReadF10.fin10 sp0 p1 mb gm sec cn path content stdin0 fs0 tid Hfile R M V B e M0 K ST ltac:(lia) HspR).
        unfold UbReadF10.post_branch. apply (HPOST 10); [lia|].
        change (65536 * 2 ^ (10 - 1))%Z with 33554432%Z. change (65536 * 2 ^ 10)%Z with 67108864%Z. lia.
      - (* [comment removed for export] *)
        apply (UbReadF10.fill10 sp0 p1 mb gm sec cn path content stdin0 fs0 tid Hfile R M V B e M0 TREF ST ltac:(lia) HspR).
        unfold UbReadF10.full_branch. intros R' M' V' B' e' ST'. change (cap_of 10) with 67108864%Z.
        exact (UbReadF10.refused10 sp0 p1 mb gm sec cn path content stdin0 fs0 tid R' M' V' B' e' M0 TREF ST' HspR HREF).
    Qed.

    Lemma HS9 : forall R M V B e, half 9 sp0 p1 mb gm sec cn B e content M0 R M V -> (16777216 <= L)%Z ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x13b8c) M (seg_rom RSEGS)) (modelG (held_of 9) V)) SH9.
    Proof.
      intros R M V B e ST HGE. unfold SH9. change (held_of 9) with 16777216%Z.
      destruct (Z.ltb_spec L 33554432) as [HLT|HGE2].
      - (* [comment removed for export] *)
        apply (UbReadF9.fin9 sp0 p1 mb gm sec cn path content stdin0 fs0 tid Hfile R M V B e M0 K ST ltac:(lia) HspR).
        unfold UbReadF9.post_branch. apply (HPOST 9); [lia|].
        change (65536 * 2 ^ (9 - 1))%Z with 16777216%Z. change (65536 * 2 ^ 9)%Z with 33554432%Z. lia.
      - (* [comment removed for export] *)
        apply (UbReadF9.fill9 sp0 p1 mb gm sec cn path content stdin0 fs0 tid Hfile R M V B e M0 (t_alt2 TOOM SH10) ST ltac:(lia) HspR).
        unfold UbReadF9.full_branch. intros R' M' V' B' e' ST'. change (cap_of 9) with 33554432%Z.
        apply (UbReadG9.grow9 sp0 p1 mb gm sec cn path content stdin0 fs0 tid R' M' V' B' e' M0 SH10 TOOM ST' ltac:(lia) Hmb0 Hmb1 Hmba HspR HOOM).
        unfold UbReadG9.half_branch. intros R'' M'' V'' B'' e'' ST''. apply (HS10 R'' M'' V'' B'' e'' ST''). lia.
    Qed.

    Lemma HS8 : forall R M V B e, half 8 sp0 p1 mb gm sec cn B e content M0 R M V -> (8388608 <= L)%Z ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x13b8c) M (seg_rom RSEGS)) (modelG (held_of 8) V)) SH8.
    Proof.
      intros R M V B e ST HGE. unfold SH8. change (held_of 8) with 8388608%Z.
      destruct (Z.ltb_spec L 16777216) as [HLT|HGE2].
      - (* [comment removed for export] *)
        apply (UbReadF8.fin8 sp0 p1 mb gm sec cn path content stdin0 fs0 tid Hfile R M V B e M0 K ST ltac:(lia) HspR).
        unfold UbReadF8.post_branch. apply (HPOST 8); [lia|].
        change (65536 * 2 ^ (8 - 1))%Z with 8388608%Z. change (65536 * 2 ^ 8)%Z with 16777216%Z. lia.
      - (* [comment removed for export] *)
        apply (UbReadF8.fill8 sp0 p1 mb gm sec cn path content stdin0 fs0 tid Hfile R M V B e M0 (t_alt2 TOOM SH9) ST ltac:(lia) HspR).
        unfold UbReadF8.full_branch. intros R' M' V' B' e' ST'. change (cap_of 8) with 16777216%Z.
        apply (UbReadG8.grow8 sp0 p1 mb gm sec cn path content stdin0 fs0 tid R' M' V' B' e' M0 SH9 TOOM ST' ltac:(lia) Hmb0 Hmb1 Hmba HspR HOOM).
        unfold UbReadG8.half_branch. intros R'' M'' V'' B'' e'' ST''. apply (HS9 R'' M'' V'' B'' e'' ST''). lia.
    Qed.

    Lemma HS7 : forall R M V B e, half 7 sp0 p1 mb gm sec cn B e content M0 R M V -> (4194304 <= L)%Z ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x13b8c) M (seg_rom RSEGS)) (modelG (held_of 7) V)) SH7.
    Proof.
      intros R M V B e ST HGE. unfold SH7. change (held_of 7) with 4194304%Z.
      destruct (Z.ltb_spec L 8388608) as [HLT|HGE2].
      - (* [comment removed for export] *)
        apply (UbReadF7.fin7 sp0 p1 mb gm sec cn path content stdin0 fs0 tid Hfile R M V B e M0 K ST ltac:(lia) HspR).
        unfold UbReadF7.post_branch. apply (HPOST 7); [lia|].
        change (65536 * 2 ^ (7 - 1))%Z with 4194304%Z. change (65536 * 2 ^ 7)%Z with 8388608%Z. lia.
      - (* [comment removed for export] *)
        apply (UbReadF7.fill7 sp0 p1 mb gm sec cn path content stdin0 fs0 tid Hfile R M V B e M0 (t_alt2 TOOM SH8) ST ltac:(lia) HspR).
        unfold UbReadF7.full_branch. intros R' M' V' B' e' ST'. change (cap_of 7) with 8388608%Z.
        apply (UbReadG7.grow7 sp0 p1 mb gm sec cn path content stdin0 fs0 tid R' M' V' B' e' M0 SH8 TOOM ST' ltac:(lia) Hmb0 Hmb1 Hmba HspR HOOM).
        unfold UbReadG7.half_branch. intros R'' M'' V'' B'' e'' ST''. apply (HS8 R'' M'' V'' B'' e'' ST''). lia.
    Qed.

    Lemma HS6 : forall R M V B e, half 6 sp0 p1 mb gm sec cn B e content M0 R M V -> (2097152 <= L)%Z ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x13b8c) M (seg_rom RSEGS)) (modelG (held_of 6) V)) SH6.
    Proof.
      intros R M V B e ST HGE. unfold SH6. change (held_of 6) with 2097152%Z.
      destruct (Z.ltb_spec L 4194304) as [HLT|HGE2].
      - (* [comment removed for export] *)
        apply (UbReadF6.fin6 sp0 p1 mb gm sec cn path content stdin0 fs0 tid Hfile R M V B e M0 K ST ltac:(lia) HspR).
        unfold UbReadF6.post_branch. apply (HPOST 6); [lia|].
        change (65536 * 2 ^ (6 - 1))%Z with 2097152%Z. change (65536 * 2 ^ 6)%Z with 4194304%Z. lia.
      - (* [comment removed for export] *)
        apply (UbReadF6.fill6 sp0 p1 mb gm sec cn path content stdin0 fs0 tid Hfile R M V B e M0 (t_alt2 TOOM SH7) ST ltac:(lia) HspR).
        unfold UbReadF6.full_branch. intros R' M' V' B' e' ST'. change (cap_of 6) with 4194304%Z.
        apply (UbReadG6.grow6 sp0 p1 mb gm sec cn path content stdin0 fs0 tid R' M' V' B' e' M0 SH7 TOOM ST' ltac:(lia) Hmb0 Hmb1 Hmba HspR HOOM).
        unfold UbReadG6.half_branch. intros R'' M'' V'' B'' e'' ST''. apply (HS7 R'' M'' V'' B'' e'' ST''). lia.
    Qed.

    Lemma HS5 : forall R M V B e, half 5 sp0 p1 mb gm sec cn B e content M0 R M V -> (1048576 <= L)%Z ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x13b8c) M (seg_rom RSEGS)) (modelG (held_of 5) V)) SH5.
    Proof.
      intros R M V B e ST HGE. unfold SH5. change (held_of 5) with 1048576%Z.
      destruct (Z.ltb_spec L 2097152) as [HLT|HGE2].
      - (* [comment removed for export] *)
        apply (UbReadF5.fin5 sp0 p1 mb gm sec cn path content stdin0 fs0 tid Hfile R M V B e M0 K ST ltac:(lia) HspR).
        unfold UbReadF5.post_branch. apply (HPOST 5); [lia|].
        change (65536 * 2 ^ (5 - 1))%Z with 1048576%Z. change (65536 * 2 ^ 5)%Z with 2097152%Z. lia.
      - (* [comment removed for export] *)
        apply (UbReadF5.fill5 sp0 p1 mb gm sec cn path content stdin0 fs0 tid Hfile R M V B e M0 (t_alt2 TOOM SH6) ST ltac:(lia) HspR).
        unfold UbReadF5.full_branch. intros R' M' V' B' e' ST'. change (cap_of 5) with 2097152%Z.
        apply (UbReadG5.grow5 sp0 p1 mb gm sec cn path content stdin0 fs0 tid R' M' V' B' e' M0 SH6 TOOM ST' ltac:(lia) Hmb0 Hmb1 Hmba HspR HOOM).
        unfold UbReadG5.half_branch. intros R'' M'' V'' B'' e'' ST''. apply (HS6 R'' M'' V'' B'' e'' ST''). lia.
    Qed.

    Lemma HS4 : forall R M V B e, half 4 sp0 p1 mb gm sec cn B e content M0 R M V -> (524288 <= L)%Z ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x13b8c) M (seg_rom RSEGS)) (modelG (held_of 4) V)) SH4.
    Proof.
      intros R M V B e ST HGE. unfold SH4. change (held_of 4) with 524288%Z.
      destruct (Z.ltb_spec L 1048576) as [HLT|HGE2].
      - (* [comment removed for export] *)
        apply (UbReadF4.fin4 sp0 p1 mb gm sec cn path content stdin0 fs0 tid Hfile R M V B e M0 K ST ltac:(lia) HspR).
        unfold UbReadF4.post_branch. apply (HPOST 4); [lia|].
        change (65536 * 2 ^ (4 - 1))%Z with 524288%Z. change (65536 * 2 ^ 4)%Z with 1048576%Z. lia.
      - (* [comment removed for export] *)
        apply (UbReadF4.fill4 sp0 p1 mb gm sec cn path content stdin0 fs0 tid Hfile R M V B e M0 (t_alt2 TOOM SH5) ST ltac:(lia) HspR).
        unfold UbReadF4.full_branch. intros R' M' V' B' e' ST'. change (cap_of 4) with 1048576%Z.
        apply (UbReadG4.grow4 sp0 p1 mb gm sec cn path content stdin0 fs0 tid R' M' V' B' e' M0 SH5 TOOM ST' ltac:(lia) Hmb0 Hmb1 Hmba HspR HOOM).
        unfold UbReadG4.half_branch. intros R'' M'' V'' B'' e'' ST''. apply (HS5 R'' M'' V'' B'' e'' ST''). lia.
    Qed.

    Lemma HS3 : forall R M V B e, half 3 sp0 p1 mb gm sec cn B e content M0 R M V -> (262144 <= L)%Z ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x13b8c) M (seg_rom RSEGS)) (modelG (held_of 3) V)) SH3.
    Proof.
      intros R M V B e ST HGE. unfold SH3. change (held_of 3) with 262144%Z.
      destruct (Z.ltb_spec L 524288) as [HLT|HGE2].
      - (* [comment removed for export] *)
        apply (UbReadF3.fin3 sp0 p1 mb gm sec cn path content stdin0 fs0 tid Hfile R M V B e M0 K ST ltac:(lia) HspR).
        unfold UbReadF3.post_branch. apply (HPOST 3); [lia|].
        change (65536 * 2 ^ (3 - 1))%Z with 262144%Z. change (65536 * 2 ^ 3)%Z with 524288%Z. lia.
      - (* [comment removed for export] *)
        apply (UbReadF3.fill3 sp0 p1 mb gm sec cn path content stdin0 fs0 tid Hfile R M V B e M0 (t_alt2 TOOM SH4) ST ltac:(lia) HspR).
        unfold UbReadF3.full_branch. intros R' M' V' B' e' ST'. change (cap_of 3) with 524288%Z.
        apply (UbReadG3.grow3 sp0 p1 mb gm sec cn path content stdin0 fs0 tid R' M' V' B' e' M0 SH4 TOOM ST' ltac:(lia) Hmb0 Hmb1 Hmba HspR HOOM).
        unfold UbReadG3.half_branch. intros R'' M'' V'' B'' e'' ST''. apply (HS4 R'' M'' V'' B'' e'' ST''). lia.
    Qed.

    Lemma HS2 : forall R M V B e, half 2 sp0 p1 mb gm sec cn B e content M0 R M V -> (131072 <= L)%Z ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x13b8c) M (seg_rom RSEGS)) (modelG (held_of 2) V)) SH2.
    Proof.
      intros R M V B e ST HGE. unfold SH2. change (held_of 2) with 131072%Z.
      destruct (Z.ltb_spec L 262144) as [HLT|HGE2].
      - (* [comment removed for export] *)
        apply (UbReadF2.fin2 sp0 p1 mb gm sec cn path content stdin0 fs0 tid Hfile R M V B e M0 K ST ltac:(lia) HspR).
        unfold UbReadF2.post_branch. apply (HPOST 2); [lia|].
        change (65536 * 2 ^ (2 - 1))%Z with 131072%Z. change (65536 * 2 ^ 2)%Z with 262144%Z. lia.
      - (* [comment removed for export] *)
        apply (UbReadF2.fill2 sp0 p1 mb gm sec cn path content stdin0 fs0 tid Hfile R M V B e M0 (t_alt2 TOOM SH3) ST ltac:(lia) HspR).
        unfold UbReadF2.full_branch. intros R' M' V' B' e' ST'. change (cap_of 2) with 262144%Z.
        apply (UbReadG2.grow2 sp0 p1 mb gm sec cn path content stdin0 fs0 tid R' M' V' B' e' M0 SH3 TOOM ST' ltac:(lia) Hmb0 Hmb1 Hmba HspR HOOM).
        unfold UbReadG2.half_branch. intros R'' M'' V'' B'' e'' ST''. apply (HS3 R'' M'' V'' B'' e'' ST''). lia.
    Qed.

    Lemma HS1 : forall R M V B e, half 1 sp0 p1 mb gm sec cn B e content M0 R M V -> (65536 <= L)%Z ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x13b8c) M (seg_rom RSEGS)) (modelG (held_of 1) V)) SH1.
    Proof.
      intros R M V B e ST HGE. unfold SH1. change (held_of 1) with 65536%Z.
      destruct (Z.ltb_spec L 131072) as [HLT|HGE2].
      - (* [comment removed for export] *)
        apply (UbReadF1.fin1 sp0 p1 mb gm sec cn path content stdin0 fs0 tid Hfile R M V B e M0 K ST ltac:(lia) HspR).
        unfold UbReadF1.post_branch. apply (HPOST 1); [lia|].
        change (65536 * 2 ^ (1 - 1))%Z with 65536%Z. change (65536 * 2 ^ 1)%Z with 131072%Z. lia.
      - (* [comment removed for export] *)
        apply (UbReadF1.fill1 sp0 p1 mb gm sec cn path content stdin0 fs0 tid Hfile R M V B e M0 (t_alt2 TOOM SH2) ST ltac:(lia) HspR).
        unfold UbReadF1.full_branch. intros R' M' V' B' e' ST'. change (cap_of 1) with 131072%Z.
        apply (UbReadG1.grow1 sp0 p1 mb gm sec cn path content stdin0 fs0 tid R' M' V' B' e' M0 SH2 TOOM ST' ltac:(lia) Hmb0 Hmb1 Hmba HspR HOOM).
        unfold UbReadG1.half_branch. intros R'' M'' V'' B'' e'' ST''. apply (HS2 R'' M'' V'' B'' e'' ST''). lia.
    Qed.

    (* [comment removed for export] *)
    Definition FINAL : TSet := if (L <? 67108864)%Z then K else TREF.

    Lemma SH10_norm : t_eq (t_alt2 TOOM SH10) (t_alt2 TOOM FINAL).
    Proof. unfold SH10, FINAL. apply t_eq_refl. Qed.

    Lemma SH9_norm : t_eq (t_alt2 TOOM SH9) (t_alt2 TOOM FINAL).
    Proof.
      unfold SH9. destruct (Z.ltb_spec L 33554432) as [HLT|HGE].
      - unfold FINAL. rewrite (proj2 (Z.ltb_lt _ _)) by lia. apply t_eq_refl.
      - eapply t_eq_trans; [apply t_alt2_absorb | apply SH10_norm].
    Qed.

    Lemma SH8_norm : t_eq (t_alt2 TOOM SH8) (t_alt2 TOOM FINAL).
    Proof.
      unfold SH8. destruct (Z.ltb_spec L 16777216) as [HLT|HGE].
      - unfold FINAL. rewrite (proj2 (Z.ltb_lt _ _)) by lia. apply t_eq_refl.
      - eapply t_eq_trans; [apply t_alt2_absorb | apply SH9_norm].
    Qed.

    Lemma SH7_norm : t_eq (t_alt2 TOOM SH7) (t_alt2 TOOM FINAL).
    Proof.
      unfold SH7. destruct (Z.ltb_spec L 8388608) as [HLT|HGE].
      - unfold FINAL. rewrite (proj2 (Z.ltb_lt _ _)) by lia. apply t_eq_refl.
      - eapply t_eq_trans; [apply t_alt2_absorb | apply SH8_norm].
    Qed.

    Lemma SH6_norm : t_eq (t_alt2 TOOM SH6) (t_alt2 TOOM FINAL).
    Proof.
      unfold SH6. destruct (Z.ltb_spec L 4194304) as [HLT|HGE].
      - unfold FINAL. rewrite (proj2 (Z.ltb_lt _ _)) by lia. apply t_eq_refl.
      - eapply t_eq_trans; [apply t_alt2_absorb | apply SH7_norm].
    Qed.

    Lemma SH5_norm : t_eq (t_alt2 TOOM SH5) (t_alt2 TOOM FINAL).
    Proof.
      unfold SH5. destruct (Z.ltb_spec L 2097152) as [HLT|HGE].
      - unfold FINAL. rewrite (proj2 (Z.ltb_lt _ _)) by lia. apply t_eq_refl.
      - eapply t_eq_trans; [apply t_alt2_absorb | apply SH6_norm].
    Qed.

    Lemma SH4_norm : t_eq (t_alt2 TOOM SH4) (t_alt2 TOOM FINAL).
    Proof.
      unfold SH4. destruct (Z.ltb_spec L 1048576) as [HLT|HGE].
      - unfold FINAL. rewrite (proj2 (Z.ltb_lt _ _)) by lia. apply t_eq_refl.
      - eapply t_eq_trans; [apply t_alt2_absorb | apply SH5_norm].
    Qed.

    Lemma SH3_norm : t_eq (t_alt2 TOOM SH3) (t_alt2 TOOM FINAL).
    Proof.
      unfold SH3. destruct (Z.ltb_spec L 524288) as [HLT|HGE].
      - unfold FINAL. rewrite (proj2 (Z.ltb_lt _ _)) by lia. apply t_eq_refl.
      - eapply t_eq_trans; [apply t_alt2_absorb | apply SH4_norm].
    Qed.

    Lemma SH2_norm : t_eq (t_alt2 TOOM SH2) (t_alt2 TOOM FINAL).
    Proof.
      unfold SH2. destruct (Z.ltb_spec L 262144) as [HLT|HGE].
      - unfold FINAL. rewrite (proj2 (Z.ltb_lt _ _)) by lia. apply t_eq_refl.
      - eapply t_eq_trans; [apply t_alt2_absorb | apply SH3_norm].
    Qed.

    Lemma SH1_norm : t_eq (t_alt2 TOOM SH1) (t_alt2 TOOM FINAL).
    Proof.
      unfold SH1. destruct (Z.ltb_spec L 131072) as [HLT|HGE].
      - unfold FINAL. rewrite (proj2 (Z.ltb_lt _ _)) by lia. apply t_eq_refl.
      - eapply t_eq_trans; [apply t_alt2_absorb | apply SH2_norm].
    Qed.

  End Stages.

  Theorem read_big : forall R M VM K TOOM TREF,
    read_pre sp0 p1 mb gm sec cn R M -> vm_pre VM sp0 mb gm ->
    (forall i, (0 <= i < 0x1000)%Z -> M (Z_to_bv 64 i) = None) ->
    (65536 <= L)%Z ->
    UbReadStage.oom_branch sp0 path stdin0 fs0 tid M TOOM ->
    (forall R' M' off V', oom_leaf sp0 M R' M' ->
       realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x13d08) M' (seg_rom RSEGS)) (modelG off V')) TREF) ->
    (forall k, (1 <= k <= 10)%Z -> (65536 * 2 ^ (k - 1) <= L < 65536 * 2 ^ k)%Z -> post_cont k M K) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x13b14) M (seg_rom RSEGS)) (modelG 0 VM))
             (t_alt2 TOOM (if (L <? 67108864)%Z then K else TREF)).
  Proof.
    intros R M VM K TOOM TREF RP VP Hpage0 HL64 HOOM HREF HPOST.
    pose proof (rp_sp0 _ _ _ _ _ _ _ _ RP) as Hsp. pose proof (rp_b _ _ _ _ _ _ _ _ RP) as Hmb. pose proof (rp_gm _ _ _ _ _ _ _ _ RP) as Hgm.
    destruct (rp_errno _ _ _ _ _ _ _ _ RP) as [e He].
    apply (rz_conseq RSEGS _ (t_alt2 TOOM (SH1 K TOOM TREF))).
    - change (modelG 0 VM) with (model_pre path VM stdin0 fs0 tid).
      apply (UbRead0.read_full0 sp0 p1 mb gm sec cn path content VM stdin0 fs0 tid Hfile R M _ e RP HL64 He Hpage0).
      intros R' M' F0 _.
      apply (UbReadG0.grow0 sp0 p1 mb gm sec cn path content VM stdin0 fs0 tid R' M' e M (SH1 K TOOM TREF) TOOM F0 VP HL64
               (proj1 Hsp) (proj1 Hmb) (proj1 (proj2 Hmb)) (proj2 (proj2 Hmb)) (proj1 Hgm) (proj1 (proj2 Hgm)) (proj2 (proj2 Hgm)) HOOM).
      unfold UbReadG0.half1_branch. intros R'' M'' V'' B'' e'' ST''.
      apply (HS1 M K TOOM TREF (proj1 Hmb) (proj1 (proj2 Hmb)) (proj2 (proj2 Hmb)) (proj1 Hsp) HOOM HREF HPOST R'' M'' V'' B'' e'' ST''). lia.
    - change (if (L <? 67108864)%Z then K else TREF) with (FINAL K TREF).
      apply (SH1_norm K TOOM TREF).
  Qed.
End Big.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
