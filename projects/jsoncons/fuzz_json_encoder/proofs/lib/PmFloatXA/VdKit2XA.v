(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan HeapIface HeapIfaceA L5Defs L5Core L5LazyA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutAuto CutLib CutHeap CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutHeapV.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmEncSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmAsanKit Require Import PtKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require Import EncKitA EncBridgesA EncHtransA EncStransA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module VDK2.
Definition mem := (word -> option byte).

Section Inst.
Import PMES.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable IC : PMLA.consts.
Variable EC : PMESA.econsts.
Variables V S2 : Z.
Hypothesis AP : PMLA.apart V ENC_SIZE S2 24.

Lemma enc_inv_grown_w : forall (M' M2 : mem) g rep' n LBk FFk spc scr Wx,
  PMESA.enc_invA L IC EC M' V S2 g -> CHA.ahpres L ar LBk FFk spc scr ((S2, 24) :: Wx) M' M2 ->
  (forall w a, In w Wx -> L5.in_rng w a -> ~ (V <= a < V + 408) /\ ~ (g_sb g <= a < g_sb g + g_scap g) /\ ~ (BIGSHADOW_LO <= a < BIGSHADOW_HI)) ->
  (exists f, In f FFk /\ ff_addr f + 32 <= V /\ V + 408 <= ff_addr f + ff_bytes (ff_class f) - 8) ->
  (S2 + 24 <= BIGSHADOW_LO \/ BIGSHADOW_HI <= S2) ->
  (forall b, In b (stack_blocks (g_sb g) (g_scap g)) -> In b LBk /\ PMLA.apart (fst b) (snd b) S2 24) ->
  PMESA.sink_atA L M2 S2 rep' -> len (PML.srep_chars rep') = g_len g + n ->
  (forall b, In b (PML.srep_blocks rep') -> 0 <= fst b /\ fst b mod 16 = 0 /\ 0 < snd b /\ fst b + snd b <= 2 ^ 47) ->
  PMESA.enc_invA L IC EC M2 V S2 (EBA.g_upd g rep' n).
Proof.
  intros M' M2 g rep' n LBk FFk spc scr Wx INV (HP1 & HP2 & HP3) WX (f & Hf & Vf1 & Vf2) S2app HSB Hsink Hlen Hnew.
  pose proof INV as (I1 & I2 & I3 & I4 & I5 & I6 & (R1 & R2 & R3 & R4 & RB)). unfold ENC_SIZE in R2.
  unfold PMLA.apart, ENC_SIZE in AP.
  assert (KV : forall a, V <= a < V + 408 -> M2 (Z_to_bv 64 a) = M' (Z_to_bv 64 a)).
  { intros a Ha. apply HP1. split; [lia|]. split; [do 3 right; left; exists f; split; [exact Hf | lia]|].
    intros w [<-|Hw]; [unfold L5.in_rng; cbn [fst snd]; lia|]. intros Hin. exact (proj1 (WX w a Hw Hin) Ha). }
  assert (AV : forall a n0, V <= a -> a + n0 <= V + 408 -> L5C.agree_on M' M2 a n0) by (intros a n0 H1 H2 i Hi; apply KV; lia).
  assert (STB : forall b, In b (stack_blocks (g_sb g) (g_scap g)) -> In b (g_lbv g)) by (intros b Hb; unfold g_lbv; apply in_or_app; right; exact Hb).
  unfold EBA.g_upd. split; [|split; [|split; [|split; [exact Hsink | split; [exact Hlen | split; [exact I6|]]]]]]; cbn [g_es g_len g_rep g_sb g_scap].
  - apply (EKA.enc_obj_agree L IC EC M' M2 V S2 _ R1 ltac:(unfold ENC_SIZE; lia)); [apply AV; unfold O_COLUMN; lia | apply AV; unfold O_COLON, ENC_SIZE; lia | | exact I1].
    apply (L5C.defined_agree M' M2 (V + O_COLUMN) 8); [apply AV; unfold O_COLUMN; lia|].
    destruct I1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). exact X.
  - apply (EKA.stack_at_agree L M' M2 V _ _ _ R1 ltac:(unfold ENC_SIZE; lia)); [apply AV; unfold O_STACK; lia | | exact I2].
    intros Hne. assert (Hin : In (g_sb g, g_scap g) (stack_blocks (g_sb g) (g_scap g))).
    { unfold stack_blocks. destruct (Z.eqb_spec (g_scap g) 0) as [E|E]; [contradiction | left; reflexivity]. }
    destruct (HSB _ Hin) as [HinK HapS]. destruct (RB _ (STB _ Hin)) as (B0 & B1 & B2 & B3). cbn [fst snd] in *.
    split; [lia|]. split; [lia|]. intros i Hi. apply HP1. split; [lia|]. split; [left; exists (g_sb g, g_scap g); split; [exact HinK | cbn [fst snd]; lia]|].
    intros w [<-|Hw]; [unfold L5.in_rng; cbn [fst snd]; unfold PMLA.apart in HapS; lia|]. intros Hin'. exact (proj1 (proj2 (WX w _ Hw Hin')) ltac:(lia)).
  - apply (EKA.stack_sh_agree M' M2 _ _ _); [|exact I3]. intros Hne.
    assert (Hin : In (g_sb g, g_scap g) (stack_blocks (g_sb g) (g_scap g))).
    { unfold stack_blocks. destruct (Z.eqb_spec (g_scap g) 0) as [E|E]; [contradiction | left; reflexivity]. }
    destruct (HSB _ Hin) as [HinK HapS]. destruct (RB _ (STB _ Hin)) as (B0 & B1 & B2 & B3). cbn [fst snd] in *.
    destruct I2 as (_ & _ & _ & S4 & S5 & _).
    assert (C8 : g_scap g mod 8 = 0) by (destruct S5 as [[E _]|(k & Hk & ->)]; [contradiction | apply EKA.mul32_mod8; lia]).
    assert (B8 : g_sb g mod 8 = 0) by (apply Z.mod_divide in B1; [|lia]; destruct B1 as [q ->]; replace (q * 16) with ((q * 2) * 8) by lia; apply Z_mod_mult).
    split; [exact B8|]. split; [exact C8|]. split; [pose proof (EKA.depth_nonneg (g_es g)); lia|].
    intros j Hj. apply HP1.
    assert (C32 : 32 <= g_scap g) by (destruct S5 as [[E _]|(k & Hk & E)]; [contradiction | pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)); nia]).
    assert (G4 : 4 <= g_scap g / 8) by (apply Z.div_le_lower_bound; lia).
    pose proof (CL5A.shreg_in_shadow (g_sb g) (g_scap g / 8) (S (g_sb g) + j) B8 ltac:(lia) ltac:(unfold S; lia)) as SH.
    replace (8 * (g_scap g / 8)) with (g_scap g) in SH by (apply Z.mod_divide in C8; [|lia]; destruct C8 as [q Hq]; rewrite Hq at 1; rewrite Hq; rewrite Z.div_mul; lia).
    pose proof (CHA.shadow_range (g_sb g) (g_scap g) (S (g_sb g) + j) B0 ltac:(lia) B3 SH) as SR.
    split; [lia|]. split; [do 6 right; exists (g_sb g, g_scap g); split; [exact HinK | exact SH]|].
    intros w [<-|Hw]; [unfold L5.in_rng; cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI in S2app; lia|]. intros Hin'.
    exact (proj2 (proj2 (WX w _ Hw Hin')) ltac:(unfold BIGSHADOW_LO, BIGSHADOW_HI in SR |- *; lia)).
  - split; [exact R1|]. split; [unfold ENC_SIZE; lia|]. split; [exact R3|]. split; [exact R4|].
    intros b Hb. unfold g_lbv in Hb. cbn [g_rep g_sb g_scap] in Hb. apply in_app_or in Hb as [Hb|Hb]; [exact (Hnew b Hb) | exact (RB b (STB b Hb))].
Qed.
End Inst.
End VDK2.
