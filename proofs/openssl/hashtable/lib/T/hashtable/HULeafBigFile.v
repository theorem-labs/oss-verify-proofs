(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ModelAmb.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes ShapeLaws MmapSim AllocSim FileSim AgentLib MemSplit Frame
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib RefNodes ExistsRun PhaseG LibKnowFrame LibKnowXfer RefReadLib
  Spec HUTargetPre HUWorld HUWorldK HUReadBase HUReadStage HUReadChunk HURead0 HUReadG0 HUReadG1 HUReadG4 HUReadG7 HUReadF1
  HUHeader_defs HULeafHeader HUHeaderK HUTargetFull.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)
Import ListNotations.
Import ConeCfg.
Open Scope bv_scope.
Import SX2. Import SX2S.
Import ConeCfg.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Module H0ReadBig.

Section Big.
  Variables (sp0 p1 mb bw gm can sec : word) (path content : list byte).
  Variables (stdin0 : AmbIn) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (HUReadStage.modelG path stdin0 fs0 tid) (only parsing).

  (* [comment removed for export] *)
  Definition post_cont (mode : bool) (Q : config -> Prop) (k : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, read_post k sp0 p1 mb bw gm B e can sec content M0 R M V ->
      GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1aa0) M (seg_rom RSEGS)) (model_post V stdin0 fs0 tid)).

  Section Stages.
    Variables (mode : bool) (Q : config -> Prop) (M0 : word -> option byte) (K TOOM TREF : TSet).
    Hypothesis Hmb0 : (0x1000 <= bv_unsigned mb)%Z.
    Hypothesis Hmb1 : (bv_unsigned mb + 8192 <= bv_unsigned sp0 - 8388608)%Z.
    Hypothesis Hmba : (bv_unsigned mb mod 4096 = 0)%Z.
    Hypothesis HspR : (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z.
    Hypothesis HOOM : mode = true -> HUReadStage.oom_branch sp0 path stdin0 fs0 tid M0 TOOM.
    Hypothesis HREF : mode = true -> forall R' M' off V', oom_leaf sp0 M0 R' M' ->
      realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0xe1bf8) M' (seg_rom RSEGS)) (modelG off V')) TREF.
    Hypothesis HLT : mode = false -> (L < 67108864)%Z.
    Hypothesis HPOST : forall k, (1 <= k <= 10)%Z -> (65536 * 2 ^ (k - 1) <= L < 65536 * 2 ^ k)%Z -> post_cont mode Q k M0 K.

    (* [comment removed for export] *)
    Definition SH10 : TSet := if (L <? 67108864)%Z then K else TREF.
    Definition SH9 : TSet := if (L <? 33554432)%Z then K else SH10.
    Definition SH8 : TSet := if (L <? 16777216)%Z then K else SH9.
    Definition SH7 : TSet := if (L <? 8388608)%Z then K else SH8.
    Definition SH6 : TSet := if (L <? 4194304)%Z then K else SH7.
    Definition SH5 : TSet := if (L <? 2097152)%Z then K else SH6.
    Definition SH4 : TSet := if (L <? 1048576)%Z then K else SH5.
    Definition SH3 : TSet := if (L <? 524288)%Z then K else SH4.
    Definition SH2 : TSet := if (L <? 262144)%Z then K else SH3.
    Definition SH1 : TSet := if (L <? 131072)%Z then K else SH2.

    Lemma HS10 : forall R M V B e, half 10 sp0 p1 mb bw gm L B e can sec content M0 R M V -> (33554432 <= L)%Z ->
      GG RSEGS mode Q SH10 (mkCfg (mkst R (Z_to_bv 64 0xe1a68) M (seg_rom RSEGS)) (modelG (held_of 10) V)).
    Proof.
      intros R M V B e ST HGE. unfold SH10. change (held_of 10) with 33554432%Z.
      destruct (Z.ltb_spec L 67108864) as [HLT'|HGE2].
      - (* [comment removed for export] *)
        apply (HUReadF1.H0ReadF10.fin10 sp0 p1 mb bw gm can sec path content stdin0 fs0 tid Hfile mode Q R M V B e M0 K ST ltac:(lia) HspR).
        unfold HUReadF1.H0ReadF10.post_branch. apply (HPOST 10); [lia|].
        change (65536 * 2 ^ (10 - 1))%Z with 33554432%Z. change (65536 * 2 ^ 10)%Z with 67108864%Z. lia.
      - (* [comment removed for export] *)
        destruct mode; [| exfalso; pose proof (HLT eq_refl); lia].
        apply (HUReadF1.H0ReadF10.fill10 sp0 p1 mb bw gm can sec path content stdin0 fs0 tid Hfile true Q R M V B e M0 TREF ST ltac:(lia) HspR).
        unfold HUReadF1.H0ReadF10.full_branch. intros R' M' V' B' e' ST'. change (cap_of 10) with 67108864%Z.
        apply gg_of_rz.
        exact (HUReadF1.H0ReadF10.refused10 sp0 p1 mb bw gm can sec path content stdin0 fs0 tid R' M' V' B' e' M0 TREF ST' HspR (HREF eq_refl)).
    Qed.

    Lemma HS9 : forall R M V B e, half 9 sp0 p1 mb bw gm L B e can sec content M0 R M V -> (16777216 <= L)%Z ->
      GG RSEGS mode Q SH9 (mkCfg (mkst R (Z_to_bv 64 0xe1a68) M (seg_rom RSEGS)) (modelG (held_of 9) V)).
    Proof.
      intros R M V B e ST HGE. unfold SH9. change (held_of 9) with 16777216%Z.
      destruct (Z.ltb_spec L 33554432) as [HLT'|HGE2].
      - (* [comment removed for export] *)
        apply (HUReadF1.H0ReadF9.fin9 sp0 p1 mb bw gm can sec path content stdin0 fs0 tid Hfile mode Q R M V B e M0 K ST ltac:(lia) HspR).
        unfold HUReadF1.H0ReadF9.post_branch. apply (HPOST 9); [lia|].
        change (65536 * 2 ^ (9 - 1))%Z with 16777216%Z. change (65536 * 2 ^ 9)%Z with 33554432%Z. lia.
      - (* [comment removed for export] *)
        apply (HUReadF1.H0ReadF9.fill9 sp0 p1 mb bw gm can sec path content stdin0 fs0 tid Hfile mode Q R M V B e M0 SH10 ST ltac:(lia) HspR).
        unfold HUReadF1.H0ReadF9.full_branch. intros R' M' V' B' e' ST'. change (cap_of 9) with 33554432%Z.
        apply (HUReadG7.H0ReadG9.grow9 sp0 p1 mb bw gm can sec path content stdin0 fs0 tid mode Q R' M' V' B' e' M0 SH10 TOOM ST' ltac:(lia) Hmb0 Hmb1 Hmba HspR HOOM).
        unfold HUReadG7.H0ReadG9.half_branch. intros R'' M'' V'' B'' e'' ST''. apply (HS10 R'' M'' V'' B'' e'' ST''). lia.
    Qed.

    Lemma HS8 : forall R M V B e, half 8 sp0 p1 mb bw gm L B e can sec content M0 R M V -> (8388608 <= L)%Z ->
      GG RSEGS mode Q SH8 (mkCfg (mkst R (Z_to_bv 64 0xe1a68) M (seg_rom RSEGS)) (modelG (held_of 8) V)).
    Proof.
      intros R M V B e ST HGE. unfold SH8. change (held_of 8) with 8388608%Z.
      destruct (Z.ltb_spec L 16777216) as [HLT'|HGE2].
      - (* [comment removed for export] *)
        apply (HUReadF1.H0ReadF8.fin8 sp0 p1 mb bw gm can sec path content stdin0 fs0 tid Hfile mode Q R M V B e M0 K ST ltac:(lia) HspR).
        unfold HUReadF1.H0ReadF8.post_branch. apply (HPOST 8); [lia|].
        change (65536 * 2 ^ (8 - 1))%Z with 8388608%Z. change (65536 * 2 ^ 8)%Z with 16777216%Z. lia.
      - (* [comment removed for export] *)
        apply (HUReadF1.H0ReadF8.fill8 sp0 p1 mb bw gm can sec path content stdin0 fs0 tid Hfile mode Q R M V B e M0 SH9 ST ltac:(lia) HspR).
        unfold HUReadF1.H0ReadF8.full_branch. intros R' M' V' B' e' ST'. change (cap_of 8) with 16777216%Z.
        apply (HUReadG7.H0ReadG8.grow8 sp0 p1 mb bw gm can sec path content stdin0 fs0 tid mode Q R' M' V' B' e' M0 SH9 TOOM ST' ltac:(lia) Hmb0 Hmb1 Hmba HspR HOOM).
        unfold HUReadG7.H0ReadG8.half_branch. intros R'' M'' V'' B'' e'' ST''. apply (HS9 R'' M'' V'' B'' e'' ST''). lia.
    Qed.

    Lemma HS7 : forall R M V B e, half 7 sp0 p1 mb bw gm L B e can sec content M0 R M V -> (4194304 <= L)%Z ->
      GG RSEGS mode Q SH7 (mkCfg (mkst R (Z_to_bv 64 0xe1a68) M (seg_rom RSEGS)) (modelG (held_of 7) V)).
    Proof.
      intros R M V B e ST HGE. unfold SH7. change (held_of 7) with 4194304%Z.
      destruct (Z.ltb_spec L 8388608) as [HLT'|HGE2].
      - (* [comment removed for export] *)
        apply (HUReadF1.H0ReadF7.fin7 sp0 p1 mb bw gm can sec path content stdin0 fs0 tid Hfile mode Q R M V B e M0 K ST ltac:(lia) HspR).
        unfold HUReadF1.H0ReadF7.post_branch. apply (HPOST 7); [lia|].
        change (65536 * 2 ^ (7 - 1))%Z with 4194304%Z. change (65536 * 2 ^ 7)%Z with 8388608%Z. lia.
      - (* [comment removed for export] *)
        apply (HUReadF1.H0ReadF7.fill7 sp0 p1 mb bw gm can sec path content stdin0 fs0 tid Hfile mode Q R M V B e M0 SH8 ST ltac:(lia) HspR).
        unfold HUReadF1.H0ReadF7.full_branch. intros R' M' V' B' e' ST'. change (cap_of 7) with 8388608%Z.
        apply (HUReadG7.grow7 sp0 p1 mb bw gm can sec path content stdin0 fs0 tid mode Q R' M' V' B' e' M0 SH8 TOOM ST' ltac:(lia) Hmb0 Hmb1 Hmba HspR HOOM).
        unfold HUReadG7.half_branch. intros R'' M'' V'' B'' e'' ST''. apply (HS8 R'' M'' V'' B'' e'' ST''). lia.
    Qed.

    Lemma HS6 : forall R M V B e, half 6 sp0 p1 mb bw gm L B e can sec content M0 R M V -> (2097152 <= L)%Z ->
      GG RSEGS mode Q SH6 (mkCfg (mkst R (Z_to_bv 64 0xe1a68) M (seg_rom RSEGS)) (modelG (held_of 6) V)).
    Proof.
      intros R M V B e ST HGE. unfold SH6. change (held_of 6) with 2097152%Z.
      destruct (Z.ltb_spec L 4194304) as [HLT'|HGE2].
      - (* [comment removed for export] *)
        apply (HUReadF1.H0ReadF6.fin6 sp0 p1 mb bw gm can sec path content stdin0 fs0 tid Hfile mode Q R M V B e M0 K ST ltac:(lia) HspR).
        unfold HUReadF1.H0ReadF6.post_branch. apply (HPOST 6); [lia|].
        change (65536 * 2 ^ (6 - 1))%Z with 2097152%Z. change (65536 * 2 ^ 6)%Z with 4194304%Z. lia.
      - (* [comment removed for export] *)
        apply (HUReadF1.H0ReadF6.fill6 sp0 p1 mb bw gm can sec path content stdin0 fs0 tid Hfile mode Q R M V B e M0 SH7 ST ltac:(lia) HspR).
        unfold HUReadF1.H0ReadF6.full_branch. intros R' M' V' B' e' ST'. change (cap_of 6) with 4194304%Z.
        apply (HUReadG4.H0ReadG6.grow6 sp0 p1 mb bw gm can sec path content stdin0 fs0 tid mode Q R' M' V' B' e' M0 SH7 TOOM ST' ltac:(lia) Hmb0 Hmb1 Hmba HspR HOOM).
        unfold HUReadG4.H0ReadG6.half_branch. intros R'' M'' V'' B'' e'' ST''. apply (HS7 R'' M'' V'' B'' e'' ST''). lia.
    Qed.

    Lemma HS5 : forall R M V B e, half 5 sp0 p1 mb bw gm L B e can sec content M0 R M V -> (1048576 <= L)%Z ->
      GG RSEGS mode Q SH5 (mkCfg (mkst R (Z_to_bv 64 0xe1a68) M (seg_rom RSEGS)) (modelG (held_of 5) V)).
    Proof.
      intros R M V B e ST HGE. unfold SH5. change (held_of 5) with 1048576%Z.
      destruct (Z.ltb_spec L 2097152) as [HLT'|HGE2].
      - (* [comment removed for export] *)
        apply (HUReadF1.H0ReadF5.fin5 sp0 p1 mb bw gm can sec path content stdin0 fs0 tid Hfile mode Q R M V B e M0 K ST ltac:(lia) HspR).
        unfold HUReadF1.H0ReadF5.post_branch. apply (HPOST 5); [lia|].
        change (65536 * 2 ^ (5 - 1))%Z with 1048576%Z. change (65536 * 2 ^ 5)%Z with 2097152%Z. lia.
      - (* [comment removed for export] *)
        apply (HUReadF1.H0ReadF5.fill5 sp0 p1 mb bw gm can sec path content stdin0 fs0 tid Hfile mode Q R M V B e M0 SH6 ST ltac:(lia) HspR).
        unfold HUReadF1.H0ReadF5.full_branch. intros R' M' V' B' e' ST'. change (cap_of 5) with 2097152%Z.
        apply (HUReadG4.H0ReadG5.grow5 sp0 p1 mb bw gm can sec path content stdin0 fs0 tid mode Q R' M' V' B' e' M0 SH6 TOOM ST' ltac:(lia) Hmb0 Hmb1 Hmba HspR HOOM).
        unfold HUReadG4.H0ReadG5.half_branch. intros R'' M'' V'' B'' e'' ST''. apply (HS6 R'' M'' V'' B'' e'' ST''). lia.
    Qed.

    Lemma HS4 : forall R M V B e, half 4 sp0 p1 mb bw gm L B e can sec content M0 R M V -> (524288 <= L)%Z ->
      GG RSEGS mode Q SH4 (mkCfg (mkst R (Z_to_bv 64 0xe1a68) M (seg_rom RSEGS)) (modelG (held_of 4) V)).
    Proof.
      intros R M V B e ST HGE. unfold SH4. change (held_of 4) with 524288%Z.
      destruct (Z.ltb_spec L 1048576) as [HLT'|HGE2].
      - (* [comment removed for export] *)
        apply (HUReadF1.H0ReadF4.fin4 sp0 p1 mb bw gm can sec path content stdin0 fs0 tid Hfile mode Q R M V B e M0 K ST ltac:(lia) HspR).
        unfold HUReadF1.H0ReadF4.post_branch. apply (HPOST 4); [lia|].
        change (65536 * 2 ^ (4 - 1))%Z with 524288%Z. change (65536 * 2 ^ 4)%Z with 1048576%Z. lia.
      - (* [comment removed for export] *)
        apply (HUReadF1.H0ReadF4.fill4 sp0 p1 mb bw gm can sec path content stdin0 fs0 tid Hfile mode Q R M V B e M0 SH5 ST ltac:(lia) HspR).
        unfold HUReadF1.H0ReadF4.full_branch. intros R' M' V' B' e' ST'. change (cap_of 4) with 1048576%Z.
        apply (HUReadG4.grow4 sp0 p1 mb bw gm can sec path content stdin0 fs0 tid mode Q R' M' V' B' e' M0 SH5 TOOM ST' ltac:(lia) Hmb0 Hmb1 Hmba HspR HOOM).
        unfold HUReadG4.half_branch. intros R'' M'' V'' B'' e'' ST''. apply (HS5 R'' M'' V'' B'' e'' ST''). lia.
    Qed.

    Lemma HS3 : forall R M V B e, half 3 sp0 p1 mb bw gm L B e can sec content M0 R M V -> (262144 <= L)%Z ->
      GG RSEGS mode Q SH3 (mkCfg (mkst R (Z_to_bv 64 0xe1a68) M (seg_rom RSEGS)) (modelG (held_of 3) V)).
    Proof.
      intros R M V B e ST HGE. unfold SH3. change (held_of 3) with 262144%Z.
      destruct (Z.ltb_spec L 524288) as [HLT'|HGE2].
      - (* [comment removed for export] *)
        apply (HUReadF1.H0ReadF3.fin3 sp0 p1 mb bw gm can sec path content stdin0 fs0 tid Hfile mode Q R M V B e M0 K ST ltac:(lia) HspR).
        unfold HUReadF1.H0ReadF3.post_branch. apply (HPOST 3); [lia|].
        change (65536 * 2 ^ (3 - 1))%Z with 262144%Z. change (65536 * 2 ^ 3)%Z with 524288%Z. lia.
      - (* [comment removed for export] *)
        apply (HUReadF1.H0ReadF3.fill3 sp0 p1 mb bw gm can sec path content stdin0 fs0 tid Hfile mode Q R M V B e M0 SH4 ST ltac:(lia) HspR).
        unfold HUReadF1.H0ReadF3.full_branch. intros R' M' V' B' e' ST'. change (cap_of 3) with 524288%Z.
        apply (HUReadG1.H0ReadG3.grow3 sp0 p1 mb bw gm can sec path content stdin0 fs0 tid mode Q R' M' V' B' e' M0 SH4 TOOM ST' ltac:(lia) Hmb0 Hmb1 Hmba HspR HOOM).
        unfold HUReadG1.H0ReadG3.half_branch. intros R'' M'' V'' B'' e'' ST''. apply (HS4 R'' M'' V'' B'' e'' ST''). lia.
    Qed.

    Lemma HS2 : forall R M V B e, half 2 sp0 p1 mb bw gm L B e can sec content M0 R M V -> (131072 <= L)%Z ->
      GG RSEGS mode Q SH2 (mkCfg (mkst R (Z_to_bv 64 0xe1a68) M (seg_rom RSEGS)) (modelG (held_of 2) V)).
    Proof.
      intros R M V B e ST HGE. unfold SH2. change (held_of 2) with 131072%Z.
      destruct (Z.ltb_spec L 262144) as [HLT'|HGE2].
      - (* [comment removed for export] *)
        apply (HUReadF1.H0ReadF2.fin2 sp0 p1 mb bw gm can sec path content stdin0 fs0 tid Hfile mode Q R M V B e M0 K ST ltac:(lia) HspR).
        unfold HUReadF1.H0ReadF2.post_branch. apply (HPOST 2); [lia|].
        change (65536 * 2 ^ (2 - 1))%Z with 131072%Z. change (65536 * 2 ^ 2)%Z with 262144%Z. lia.
      - (* [comment removed for export] *)
        apply (HUReadF1.H0ReadF2.fill2 sp0 p1 mb bw gm can sec path content stdin0 fs0 tid Hfile mode Q R M V B e M0 SH3 ST ltac:(lia) HspR).
        unfold HUReadF1.H0ReadF2.full_branch. intros R' M' V' B' e' ST'. change (cap_of 2) with 262144%Z.
        apply (HUReadG1.H0ReadG2.grow2 sp0 p1 mb bw gm can sec path content stdin0 fs0 tid mode Q R' M' V' B' e' M0 SH3 TOOM ST' ltac:(lia) Hmb0 Hmb1 Hmba HspR HOOM).
        unfold HUReadG1.H0ReadG2.half_branch. intros R'' M'' V'' B'' e'' ST''. apply (HS3 R'' M'' V'' B'' e'' ST''). lia.
    Qed.

    Lemma HS1 : forall R M V B e, half 1 sp0 p1 mb bw gm L B e can sec content M0 R M V -> (65536 <= L)%Z ->
      GG RSEGS mode Q SH1 (mkCfg (mkst R (Z_to_bv 64 0xe1a68) M (seg_rom RSEGS)) (modelG (held_of 1) V)).
    Proof.
      intros R M V B e ST HGE. unfold SH1. change (held_of 1) with 65536%Z.
      destruct (Z.ltb_spec L 131072) as [HLT'|HGE2].
      - (* [comment removed for export] *)
        apply (HUReadF1.fin1 sp0 p1 mb bw gm can sec path content stdin0 fs0 tid Hfile mode Q R M V B e M0 K ST ltac:(lia) HspR).
        unfold HUReadF1.post_branch. apply (HPOST 1); [lia|].
        change (65536 * 2 ^ (1 - 1))%Z with 65536%Z. change (65536 * 2 ^ 1)%Z with 131072%Z. lia.
      - (* [comment removed for export] *)
        apply (HUReadF1.fill1 sp0 p1 mb bw gm can sec path content stdin0 fs0 tid Hfile mode Q R M V B e M0 SH2 ST ltac:(lia) HspR).
        unfold HUReadF1.full_branch. intros R' M' V' B' e' ST'. change (cap_of 1) with 131072%Z.
        apply (HUReadG1.grow1 sp0 p1 mb bw gm can sec path content stdin0 fs0 tid mode Q R' M' V' B' e' M0 SH2 TOOM ST' ltac:(lia) Hmb0 Hmb1 Hmba HspR HOOM).
        unfold HUReadG1.half_branch. intros R'' M'' V'' B'' e'' ST''. apply (HS2 R'' M'' V'' B'' e'' ST''). lia.
    Qed.

    (* [comment removed for export] *)
    Definition FINAL : TSet := if (L <? 67108864)%Z then K else TREF.

    Lemma SH10_norm : t_eq SH10 FINAL.
    Proof. unfold SH10, FINAL. apply t_eq_refl. Qed.

    Lemma SH9_norm : t_eq SH9 FINAL.
    Proof.
      unfold SH9. destruct (Z.ltb_spec L 33554432) as [HLT'|HGE].
      - unfold FINAL. rewrite (proj2 (Z.ltb_lt _ _)) by lia. apply t_eq_refl.
      - apply SH10_norm.
    Qed.

    Lemma SH8_norm : t_eq SH8 FINAL.
    Proof.
      unfold SH8. destruct (Z.ltb_spec L 16777216) as [HLT'|HGE].
      - unfold FINAL. rewrite (proj2 (Z.ltb_lt _ _)) by lia. apply t_eq_refl.
      - apply SH9_norm.
    Qed.

    Lemma SH7_norm : t_eq SH7 FINAL.
    Proof.
      unfold SH7. destruct (Z.ltb_spec L 8388608) as [HLT'|HGE].
      - unfold FINAL. rewrite (proj2 (Z.ltb_lt _ _)) by lia. apply t_eq_refl.
      - apply SH8_norm.
    Qed.

    Lemma SH6_norm : t_eq SH6 FINAL.
    Proof.
      unfold SH6. destruct (Z.ltb_spec L 4194304) as [HLT'|HGE].
      - unfold FINAL. rewrite (proj2 (Z.ltb_lt _ _)) by lia. apply t_eq_refl.
      - apply SH7_norm.
    Qed.

    Lemma SH5_norm : t_eq SH5 FINAL.
    Proof.
      unfold SH5. destruct (Z.ltb_spec L 2097152) as [HLT'|HGE].
      - unfold FINAL. rewrite (proj2 (Z.ltb_lt _ _)) by lia. apply t_eq_refl.
      - apply SH6_norm.
    Qed.

    Lemma SH4_norm : t_eq SH4 FINAL.
    Proof.
      unfold SH4. destruct (Z.ltb_spec L 1048576) as [HLT'|HGE].
      - unfold FINAL. rewrite (proj2 (Z.ltb_lt _ _)) by lia. apply t_eq_refl.
      - apply SH5_norm.
    Qed.

    Lemma SH3_norm : t_eq SH3 FINAL.
    Proof.
      unfold SH3. destruct (Z.ltb_spec L 524288) as [HLT'|HGE].
      - unfold FINAL. rewrite (proj2 (Z.ltb_lt _ _)) by lia. apply t_eq_refl.
      - apply SH4_norm.
    Qed.

    Lemma SH2_norm : t_eq SH2 FINAL.
    Proof.
      unfold SH2. destruct (Z.ltb_spec L 262144) as [HLT'|HGE].
      - unfold FINAL. rewrite (proj2 (Z.ltb_lt _ _)) by lia. apply t_eq_refl.
      - apply SH3_norm.
    Qed.

    Lemma SH1_norm : t_eq SH1 FINAL.
    Proof.
      unfold SH1. destruct (Z.ltb_spec L 131072) as [HLT'|HGE].
      - unfold FINAL. rewrite (proj2 (Z.ltb_lt _ _)) by lia. apply t_eq_refl.
      - apply SH2_norm.
    Qed.

  End Stages.

  Theorem read_big : forall mode Q R M VM K TOOM TREF,
    read_pre sp0 p1 mb bw gm can sec R M -> vm_pre VM sp0 mb bw gm ->
    (forall i, (0 <= i < 0x1000)%Z -> M (Z_to_bv 64 i) = None) ->
    (65536 <= L)%Z ->
    (mode = true -> HUReadStage.oom_branch sp0 path stdin0 fs0 tid M TOOM) ->
    (mode = true -> forall R' M' off V', oom_leaf sp0 M R' M' ->
       realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0xe1bf8) M' (seg_rom RSEGS)) (modelG off V')) TREF) ->
    (mode = false -> (L < 67108864)%Z) ->
    (forall k, (1 <= k <= 10)%Z -> (65536 * 2 ^ (k - 1) <= L < 65536 * 2 ^ k)%Z -> post_cont mode Q k M K) ->
    GG RSEGS mode Q (if (L <? 67108864)%Z then K else TREF)     (* [comment removed for export] *)
       (mkCfg (mkst R (Z_to_bv 64 0xe19e0) M (seg_rom RSEGS)) (modelG 0 VM)).
  Proof.
    intros mode Q R M VM K TOOM TREF RP VP Hpage0 HL64 HOOM HREF HLT HPOST.
    pose proof (rp_sp0 _ _ _ _ _ _ _ _ _ RP) as Hsp. pose proof (rp_b _ _ _ _ _ _ _ _ _ RP) as Hmb. pose proof (rp_gm _ _ _ _ _ _ _ _ _ RP) as Hgm.
    destruct (rp_errno _ _ _ _ _ _ _ _ _ RP) as [e He].
    apply (gg_conseq RSEGS mode Q (SH1 K TREF)).
    - change (modelG 0 VM) with (model_pre path VM stdin0 fs0 tid).
      apply (HURead0.read_full0 sp0 p1 mb bw gm can sec path content VM stdin0 fs0 tid Hfile mode Q R M _ e RP HL64 He Hpage0).
      intros R' M' F0 _.
      apply (HUReadG0.grow0 sp0 p1 mb bw gm can sec path content VM stdin0 fs0 tid mode Q R' M' e M (SH1 K TREF) TOOM F0 VP HL64
               (proj1 Hsp) (proj1 Hmb) (proj1 (proj2 Hmb)) (proj2 (proj2 Hmb)) (proj1 Hgm) (proj1 (proj2 Hgm)) (proj2 (proj2 Hgm)) HOOM).
      unfold HUReadG0.half1_branch. intros R'' M'' V'' B'' e'' ST''.
      apply (HS1 mode Q M K TOOM TREF (proj1 Hmb) (proj1 (proj2 Hmb)) (proj2 (proj2 Hmb)) (proj1 Hsp) HOOM HREF HLT HPOST R'' M'' V'' B'' e'' ST''). lia.
    - change (if (L <? 67108864)%Z then K else TREF) with (FINAL K TREF).
      apply (SH1_norm K TREF).
  Qed.
End Big.

End H0ReadBig.
Import H0ReadBig.
Import ConeCfg.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section BigFile.
  Variables (sp0 p1 mb bw gm can sec : word) (R : bvmap 5 word) (M : word -> option byte).
  Variables (area brkv mas : Z) (VM : VmMaps) (path content : list byte) (stdin0 : AmbIn) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.
  Hypothesis HL : (65536 <= Z.of_nat (length content))%Z.
  Hypothesis Harea : area = (bv_unsigned mb + 4096)%Z.
  Hypothesis Hbw : bv_unsigned bw = brkv.
  Hypothesis RP : read_pre sp0 p1 mb bw gm can sec R M.
  Hypothesis W : world0 (bv_unsigned sp0) area (bv_unsigned gm) brkv mas (bv_unsigned tid) (bv_unsigned can) (bv_unsigned sec) M.
  Hypothesis VP : vm_pre VM sp0 mb bw gm.
  Hypothesis MF : main_frame (bv_unsigned sp0) M.   (* [comment removed for export] *)

  Let L : Z := Z.of_nat (length content).

  (* [comment removed for export] *)
  Theorem ref_big_file : forall mode Q (KT TOOM TREF : TSet),
    (mode = true -> HUReadStage.oom_branch sp0 path stdin0 fs0 tid M TOOM) ->
    (mode = true -> forall R' M' off V', oom_leaf sp0 M R' M' ->
       realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0xe1bf8) M' (seg_rom RSEGS)) (HUReadStage.modelG path stdin0 fs0 tid off V')) TREF) ->
    (mode = false -> (L < 67108864)%Z) ->
    (* [comment removed for export] *)
    (forall (k : Z) (B : word) (V' : VmMaps) R' M', (1 <= k <= 10)%Z ->
       tgt_entry_full sp0 k (bv_unsigned B + offk k) can content V' R' M' ->
       GG RSEGS mode Q KT (mkCfg (mkst R' (Z_to_bv 64 0xe1c8c) M' (seg_rom RSEGS)) (model_post V' stdin0 fs0 tid))) ->
    GG RSEGS mode Q (if (L <? 67108864)%Z then t_hdr content fs0 KT else TREF)     (* [comment removed for export] *)
       (mkCfg (mkst R (Z_to_bv 64 0xe19e0) M (seg_rom RSEGS)) (model_pre path VM stdin0 fs0 tid)).
  Proof.
    intros mode Q KT TOOM TREF HOOM HREF HLT HTGT.
    assert (Hvsp : valid_sp sp0).
    { pose proof (rp_sp0 _ _ _ _ _ _ _ _ _ RP) as Hs. unfold valid_sp, sp_window_lo, sp_window_hi. lia. }
    assert (Hpage0 : forall i, (0 <= i < 0x1000)%Z -> M (Z_to_bv 64 i) = None).
    { pose proof (w_img _ _ _ _ _ _ _ _ _ W) as Wi. apply (proj1 (Forall_forall _ _) Wi (0%Z, 0x1000%Z)). cbn. left. reflexivity. }
    change (model_pre path VM stdin0 fs0 tid) with (HUReadStage.modelG path stdin0 fs0 tid 0 VM).
    apply (read_big sp0 p1 mb bw gm can sec path content stdin0 fs0 tid Hfile mode Q R M VM
             (t_hdr content fs0 KT) TOOM TREF RP VP Hpage0 HL HOOM HREF HLT).
    intros k Hk Hrange. unfold post_cont. intros R' M' V' B e RQ.
    apply (header_phase_k mode Q k sp0 p1 mb bw gm B e can sec tid area brkv mas content M R' M' V' stdin0 fs0 KT Hk Hvsp RQ W).
    - unfold capk. exact Hrange.
    - intros R'' TE. apply (HTGT k B V' R'' M' Hk).
      assert (Hrange' : (capk (k - 1) <= Z.of_nat (length content) < capk k)%Z) by (unfold capk; exact Hrange).
      constructor.
      + exact TE.
      + exact (main_frame_k k sp0 p1 mb bw gm B e can sec content M R' M' V' Hvsp RQ MF).
      + exists mb, bw, B, brkv, mas, (bv_unsigned tid), (bv_unsigned sec). split; [exact Hbw|]. right.
        split; [exact Hk|]. split; [exact Hrange'|]. split; [reflexivity|]. split.
        * rewrite <- Harea.
          exact (world_k_intro k sp0 p1 mb bw gm B e can sec tid area brkv mas content M R' M' V' Hk Hvsp RQ W Hrange').
        * exact (rk_vm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RQ).
  Qed.
End BigFile.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
