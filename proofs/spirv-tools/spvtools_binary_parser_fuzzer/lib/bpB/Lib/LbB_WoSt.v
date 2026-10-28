(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame BCells BStep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec LibIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require LbB_Conv.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_PrsStmt LbB_HKit LbB_HStKit LbB_WoGen.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition mkfreshA (words n q1 q2 q3 : Z) : stateC :=
  {| st_words := words; st_nwords := n; st_diag := 0; st_widx := 0; st_icount := 0; st_endian := 0; st_flags := 0;
     st_m1 := (0, 0, []); st_m2 := (0, 0, []); st_m3 := (0, 0, []);
     st_v1 := (q1, q1, q1 + 500); st_v2 := (q2, q2, q2 + 100); st_v3 := (q3, q3, q3 + 100) |}.

Lemma vec_blocks_nzA : forall q e c, q <> 0 -> vec_blocks (q, e, c) = [(q, c - q)].
Proof. intros q e c Hq. unfold vec_blocks. cbn [HStmts.t3a HStmts.t3c fst snd]. destruct (Z.eqb_spec q 0); [lia | reflexivity]. Qed.

Lemma mkfreshA_blocks : forall words n q1 q2 q3, q1 <> 0 -> q2 <> 0 -> q3 <> 0 ->
  state_blocks (mkfreshA words n q1 q2 q3) = [(q1, 500); (q2, 100); (q3, 100)].
Proof.
  intros words n q1 q2 q3 H1 H2 H3. unfold state_blocks, mkfreshA. cbn [st_m1 st_m2 st_m3 st_v1 st_v2 st_v3 HStmts.t3a HStmts.t3b HStmts.t3c fst snd].
  rewrite !vec_blocks_nzA by assumption. cbn. repeat (f_equal; try lia).
Qed.

Lemma state_moved_mkfreshA : forall c words n q1 q2 q3, state_moved c (mkfreshA words n q1 q2 q3) = mkfreshA words n q1 q2 q3.
Proof. intros. reflexivity. Qed.
Lemma fresh_mkfreshA : forall words n q1 q2 q3, q1 <> 0 -> q2 <> 0 -> q3 <> 0 -> fresh_state (mkfreshA words n q1 q2 q3) words n.
Proof.
  intros. unfold fresh_state, mkfreshA. cbn [st_words st_nwords st_widx st_icount st_flags st_m1 st_m2 st_m3 st_v1 st_v2 st_v3 HStmts.t3a HStmts.t3b HStmts.t3c fst snd].
  repeat (split; [first [reflexivity | assumption] |]). reflexivity.
Qed.

Lemma cellw_of_rw1 : forall m a c (w : N) v, rw_cells asegs m a [c] -> csize c = N.to_nat w ->
  cbytes c = word_to_le_bytes (N.to_nat w) (Z_to_bv 64 v) -> 0 <= v < 2 ^ (8 * Z.of_N w) -> 0 <= a ->
  HRep.cellw asegs m a w v.
Proof.
  intros m a c w v Hc Hs Hb Hv Ha. split; [exact Hv|].
  pose proof (rw_cells_read asegs m a _ 0%nat _ Hc eq_refl) as RD. replace (a + Z.of_nat 0) with a in RD by lia.
  rewrite <- LbB_Conv.rdn_of_ov. rewrite Hs, Hb in RD. exact RD.
Qed.

Lemma zero_cells_sub : forall m a k o (w : nat), rw_cells asegs m a [CB k (poison_bytes k 0)] -> 0 <= o -> o + Z.of_nat w <= Z.of_nat k ->
  rw_cells asegs m (a + o) [CB w (poison_bytes w 0)].
Proof.
  intros m a k o w C Ho Hk.
  destruct (rw_cells_CB_sub m a k _ o (Z.of_nat w) C Ho ltac:(lia) Hk) as (bs & C2).
  pose proof (u8arr_of_rw_cells asegs m a k _ C) as U.
  pose proof (u8arr_sub m a _ o (Z.of_nat w) U Ho ltac:(lia) ltac:(unfold poison_bytes; rewrite repeat_length; lia)) as U2.
  unfold poison_bytes in U2. rewrite skipn_repeat', firstn_repeat' in U2.
  replace (Nat.min (Z.to_nat (Z.of_nat w)) (k - Z.to_nat o)) with w in U2 by lia.
  pose proof (rw_cells_of_u8arr asegs m _ _ U2) as C3. rewrite repeat_length in C3. exact C3.
Qed.

Lemma cellw_zero : forall m a (w : N), rw_cells asegs m a [CB (N.to_nat w) (poison_bytes (N.to_nat w) 0)] ->
  (w = 1 \/ w = 2 \/ w = 4 \/ w = 8)%N -> 0 <= a -> HRep.cellw asegs m a w 0.
Proof.
  intros m a w C Hw Ha. eapply cellw_of_rw1; [exact C | reflexivity | | | exact Ha].
  - cbn [cbytes]. destruct Hw as [->|[->|[->| ->]]]; vm_compute; reflexivity.
  - destruct Hw as [->|[->|[->| ->]]]; cbn; lia.
Qed.

Lemma cellw_zero_in : forall m a k o (w : N), rw_cells asegs m a [CB k (poison_bytes k 0)] -> 0 <= o -> o + Z.of_N w <= Z.of_nat k ->
  (w = 1 \/ w = 2 \/ w = 4 \/ w = 8)%N -> 0 <= a -> HRep.cellw asegs m (a + o) w 0.
Proof.
  intros m a k o w C Ho Hk Hw Ha. apply cellw_zero; [| exact Hw | lia].
  apply (zero_cells_sub m a k o (N.to_nat w) C Ho). lia.
Qed.

Section Fresh.
  Context {HCEIL : HeapCeil}.

  Definition st_maps_cells (m : mem) (st : Z) : Prop :=
       rw_cells asegs m (st + 48) [CB 32 (poison_bytes 32 0)] /\ rw_cells asegs m (st + 80) [C4 (Z_to_bv 64 0x3f800000)]
    /\ rw_cells asegs m (st + 88) [CB 32 (poison_bytes 32 0)] /\ rw_cells asegs m (st + 120) [C4 (Z_to_bv 64 0x3f800000)]
    /\ rw_cells asegs m (st + 128) [CB 32 (poison_bytes 32 0)] /\ rw_cells asegs m (st + 160) [C4 (Z_to_bv 64 0x3f800000)].
  Definition st_vecs_cells (m : mem) (st q1 q2 q3 : Z) : Prop :=
    rw_cells asegs m (st + 168) [C8 (Z_to_bv 64 q1); C8 (Z_to_bv 64 q1); C8 (Z_to_bv 64 (q1 + 500));
                                 C8 (Z_to_bv 64 q2); C8 (Z_to_bv 64 q2); C8 (Z_to_bv 64 (q2 + 100));
                                 C8 (Z_to_bv 64 q3); C8 (Z_to_bv 64 q3); C8 (Z_to_bv 64 (q3 + 100))].

  Definition st_scal_cells (m : mem) (st words n : Z) : Prop :=
    (words = 0 /\ n = 0 /\ rw_cells asegs m st [CB 46 (poison_bytes 46 0)])
    \/ (rw_cells asegs m st [C8 (Z_to_bv 64 words); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 0)]
        /\ rw_cells asegs m (st + 24) [CB 22 (poison_bytes 22 0)]).

  Lemma st_rep_freshA : forall LB m st words n q1 q2 q3,
    st_scal_cells m st words n -> st_maps_cells m st -> st_vecs_cells m st q1 q2 q3 ->
    0 <= words < 2 ^ 64 -> 0 <= n < 2 ^ 64 ->
    wr_at asegs m st 240 -> st mod 8 = 0 -> 0x6e8000 <= st -> st + 240 <= 2 ^ 47 ->
    0 < q1 -> q1 + 500 < 2 ^ 64 -> 0 < q2 -> q2 + 100 < 2 ^ 64 -> 0 < q3 -> q3 + 100 < 2 ^ 64 ->
    In (q1, 500) (lbl LB) -> In (q2, 100) (lbl LB) -> In (q3, 100) (lbl LB) -> NoDup [q1; q2; q3] ->
    state_repA LB m st (mkfreshA words n q1 q2 q3).
  Proof.
    intros LB m st words n q1 q2 q3 SC (M1 & F1 & M2 & F2 & M3 & F3) VC Hw Hn WR Hal Hlo Hhi Q1 Q1h Q2 Q2h Q3 Q3h I1 I2 I3 ND.
    assert (DEF : forall o k, 0 <= o -> o + k <= 240 -> defined m (st + o) k).
    { intros o k Ho Hk i Hi. pose proof (mdef_of_wr_at m st 240 WR Hlo (o + i) ltac:(lia)) as D.
      replace (st + (o + i)) with (st + o + i) in D by lia. exact D. }
    assert (Z8 : forall a o, rw_cells asegs m a [CB 32 (poison_bytes 32 0)] -> 0 <= o <= 24 -> 0 <= a -> HRep.cellw asegs m (a + o) 8 0).
    { intros a o C Ho Ha. eapply cellw_zero_in; [exact C | lia | cbn; lia | right; right; right; reflexivity | exact Ha]. }
    assert (F4 : forall a, rw_cells asegs m a [C4 (Z_to_bv 64 0x3f800000)] -> 0 <= a -> HRep.cellw asegs m a 4 0x3f800000).
    { intros a C Ha. exact (cellw4_of_rw_cells m a _ C ltac:(lia) Ha). }

    unfold st_vecs_cells in VC.
    change [C8 (Z_to_bv 64 q1); C8 (Z_to_bv 64 q1); C8 (Z_to_bv 64 (q1 + 500)); C8 (Z_to_bv 64 q2); C8 (Z_to_bv 64 q2); C8 (Z_to_bv 64 (q2 + 100));
            C8 (Z_to_bv 64 q3); C8 (Z_to_bv 64 q3); C8 (Z_to_bv 64 (q3 + 100))]
      with ([C8 (Z_to_bv 64 q1); C8 (Z_to_bv 64 q1); C8 (Z_to_bv 64 (q1 + 500))] ++ [C8 (Z_to_bv 64 q2); C8 (Z_to_bv 64 q2); C8 (Z_to_bv 64 (q2 + 100))]
            ++ [C8 (Z_to_bv 64 q3); C8 (Z_to_bv 64 q3); C8 (Z_to_bv 64 (q3 + 100))]) in VC.
    apply rw_cells_app in VC as [V1 VC]. apply rw_cells_app in VC as [V2 V3].
    cbn [cells_size csize] in V2, V3. change (Z.of_nat (8 + (8 + (8 + 0)))) with 24 in V2.
    change (Z.of_nat (8 + (8 + (8 + 0))) + Z.of_nat (8 + (8 + (8 + 0)))) with 48 in V3.
    assert (V2' : rw_cells asegs m (st + 192) [C8 (Z_to_bv 64 q2); C8 (Z_to_bv 64 q2); C8 (Z_to_bv 64 (q2 + 100))])
      by (replace (st + 192) with (st + 168 + 24) by lia; exact V2).
    assert (V3' : rw_cells asegs m (st + 216) [C8 (Z_to_bv 64 q3); C8 (Z_to_bv 64 q3); C8 (Z_to_bv 64 (q3 + 100))])
      by (replace (st + 216) with (st + 168 + 24 + 24) by lia; exact V3).
    clear V2 V3.

    assert (SCW : HRep.cellw asegs m st 8 words /\ HRep.cellw asegs m (st + 8) 8 n /\ HRep.cellw asegs m (st + 16) 8 0
                  /\ HRep.cellw asegs m (st + 24) 8 0 /\ HRep.cellw asegs m (st + 32) 8 0 /\ HRep.cellw asegs m (st + 40) 4 0
                  /\ HRep.cellw asegs m (st + 44) 2 0).
    { destruct SC as [(-> & -> & C)|(C & C24)].
      - assert (Z0 : forall o (w : N), 0 <= o -> o + Z.of_N w <= 46 -> (w = 1 \/ w = 2 \/ w = 4 \/ w = 8)%N -> HRep.cellw asegs m (st + o) w 0)
          by (intros o w Ho Hk Hw'; eapply cellw_zero_in; [exact C | exact Ho | cbn; lia | exact Hw' | lia]).
        refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))); [replace st with (st + 0) by lia| | | | | |];
          apply Z0; cbn; lia.
      - change [C8 (Z_to_bv 64 words); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 0)]
          with ([C8 (Z_to_bv 64 words)] ++ [C8 (Z_to_bv 64 n)] ++ [C8 (Z_to_bv 64 0)]) in C.
        apply rw_cells_app in C as [C0 C]. apply rw_cells_app in C as [C8' C16].
        cbn [cells_size csize] in C8', C16.
        split; [exact (cellw8_of_rw_cells m st words C0 Hw ltac:(lia))|].
        split; [exact (cellw8_of_rw_cells m (st + 8) n C8' Hn ltac:(lia))|].
        split; [replace (st + 16) with (st + Z.of_nat (8 + 0) + Z.of_nat (8 + 0)) by (cbn; lia); exact (cellw8_of_rw_cells _ _ 0 C16 ltac:(lia) ltac:(cbn; lia))|].
        replace (st + 32) with (st + 24 + 8) by lia. replace (st + 40) with (st + 24 + 16) by lia. replace (st + 44) with (st + 24 + 20) by lia.
        assert (Z0 : forall o (w : N), 0 <= o -> o + Z.of_N w <= 22 -> (w = 1 \/ w = 2 \/ w = 4 \/ w = 8)%N -> HRep.cellw asegs m (st + 24 + o) w 0)
          by (intros o w Ho Hk Hw'; eapply cellw_zero_in; [exact C24 | exact Ho | cbn; lia | exact Hw' | lia]).
        refine (conj _ (conj _ (conj _ _))); [replace (st + 24) with (st + 24 + 0) by lia| | |]; apply Z0; cbn; lia. }
    destruct SCW as (C0 & C8 & C16 & C24 & C32 & C40 & C44).
    unfold state_repA. split; [|unfold state_vstride; cbn [mkfreshA st_v1 st_v2 st_v3 HStmts.t3a HStmts.t3b fst snd]; rewrite !Z.sub_diag; repeat split; intros; reflexivity].
    constructor; cbn [mkfreshA st_words st_nwords st_diag st_widx st_icount st_endian st_flags st_m1 st_m2 st_m3 st_v1 st_v2 st_v3
                      HStmts.t3a HStmts.t3b HStmts.t3c fst snd].
    - exact C0. - exact C8. - exact C16. - exact C24. - exact C32. - exact C40. - exact C44.
    - apply (umapx_empty ASEGS LY_A MI_A 24 Z (nval24 ASEGS)); unfold cell8, cell4.
      + replace (st + 48) with (st + 48 + 0) by lia. apply Z8; [exact M1 | lia | lia].
      + apply Z8; [exact M1 | lia | lia]. + apply Z8; [exact M1 | lia | lia]. + apply Z8; [exact M1 | lia | lia].
      + replace (st + 48 + 32) with (st + 80) by lia. apply F4; [exact F1 | lia].
      + apply DEF; lia.
      + rewrite <- Zplus_mod_idemp_l, Hal. reflexivity.
      + lia. + lia.
    - apply (umapx_empty ASEGS LY_A MI_A 32 (Z * Z * Z) (nval32 ASEGS)); unfold cell8, cell4.
      + replace (st + 88) with (st + 88 + 0) by lia. apply Z8; [exact M2 | lia | lia].
      + apply Z8; [exact M2 | lia | lia]. + apply Z8; [exact M2 | lia | lia]. + apply Z8; [exact M2 | lia | lia].
      + replace (st + 88 + 32) with (st + 120) by lia. apply F4; [exact F2 | lia].
      + apply DEF; lia.
      + rewrite <- Zplus_mod_idemp_l, Hal. reflexivity.
      + lia. + lia.
    - apply (umapx_empty ASEGS LY_A MI_A 24 Z (nval24 ASEGS)); unfold cell8, cell4.
      + replace (st + 128) with (st + 128 + 0) by lia. apply Z8; [exact M3 | lia | lia].
      + apply Z8; [exact M3 | lia | lia]. + apply Z8; [exact M3 | lia | lia]. + apply Z8; [exact M3 | lia | lia].
      + replace (st + 128 + 32) with (st + 160) by lia. apply F4; [exact F3 | lia].
      + apply DEF; lia.
      + rewrite <- Zplus_mod_idemp_l, Hal. reflexivity.
      + lia. + lia.
    - apply vraw_of_rw_cells; [exact V1 | lia | lia | lia | lia | right; split; [lia | split; [replace (q1 + 500 - q1) with 500 by lia; exact I1 | lia]]].
    - apply vraw_of_rw_cells; [exact V2' | lia | lia | lia | lia | right; split; [lia | split; [replace (q2 + 100 - q2) with 100 by lia; exact I2 | lia]]].
    - apply vraw_of_rw_cells; [exact V3' | lia | lia | lia | lia | right; split; [lia | split; [replace (q3 + 100 - q3) with 100 by lia; exact I3 | lia]]].
    - replace st with (st + 0) by lia. apply DEF; lia.
    - exact Hal.
    - rewrite (mkfreshA_blocks words n q1 q2 q3) by lia. cbn [map fst]. exact ND.
  Qed.

  Lemma umap_sh_empty : forall (V : Type) m ns, umap_sh m ns (0, 0, @nil (Z * (Z * V))).
  Proof. intros V m ns. split; [intros X; exfalso; apply X; reflexivity | intros p k v []]. Qed.

  Lemma st_sh_freshA : forall m words n q1 q2 q3,
    SHAD m q1 (cc_gen 500 0) -> SHAD m q2 (cc_gen 100 0) -> SHAD m q3 (cc_gen 100 0) ->
    state_sh m (mkfreshA words n q1 q2 q3).
  Proof.
    intros m words n q1 q2 q3 S1 S2 S3. unfold state_sh, mkfreshA.
    cbn [st_m1 st_m2 st_m3 st_v1 st_v2 st_v3].
    refine (conj (umap_sh_empty _ _ _) (conj (umap_sh_empty _ _ _) (conj (umap_sh_empty _ _ _) (conj _ (conj _ _))))).
    - intros _. cbn [HStmts.t3a HStmts.t3b HStmts.t3c fst snd]. replace (q1 + 500 - q1) with 500 by lia. replace (q1 - q1) with 0 by lia. exact S1.
    - intros _. cbn [HStmts.t3a HStmts.t3b HStmts.t3c fst snd]. replace (q2 + 100 - q2) with 100 by lia. replace (q2 - q2) with 0 by lia. exact S2.
    - intros _. cbn [HStmts.t3a HStmts.t3b HStmts.t3c fst snd]. replace (q3 + 100 - q3) with 100 by lia. replace (q3 - q3) with 0 by lia. exact S3.
  Qed.
End Fresh.
