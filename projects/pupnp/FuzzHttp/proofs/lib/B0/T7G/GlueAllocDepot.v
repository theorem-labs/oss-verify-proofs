(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes Image Ceiling.
From OSSVerify.pupnp.FuzzHttp.images Require Import AsanUbsan.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import MainExport MainFactsBoth B0Img MainEntryBoth B0Handoff.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ADepot ALayout PEnv AInitReps.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7G Require Import GlueKit GlueIcpt GlueAllocKit GlueAllocLay GlueAllocBss.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition depot_h (w : bool) : Z := if w then 17443417135023758100 else 13038664596505088284.
Definition depot_tot (w : bool) : Z := if w then 3 else 2.

Section Dep.
Context {HC : HasCeiling}.
Variable V : nat -> Z.
Hypothesis AO : alayout_ok (AL_of V).
Variable m : mem.

Section Gen.
Variables (h bk tot : Z).
Hypothesis BK : bkt h = bk.
Hypothesis HR : 0 <= h < 2^64.
Hypothesis BKR : 0 <= bk < 2^20.
Hypothesis TOT : 0 <= tot <= 3.
Hypothesis IMG1 : forall i, 1598504 <= i < DT + 4 * bk -> m (wa i) = None.
Hypothesis IMG2 : forall i, DT + 4 * bk + 4 <= i < 5858328 -> m (wa i) = None.
Hypothesis BW : rw_cells asegs m (DT + 4 * bk) [C4 (wz 1)].
Hypothesis C_DNI : rw_cells asegs m DNI [C4 (wz 1)].
Hypothesis C_DM1 : rw_cells asegs m DM1 [C8 (wz (4096 * V 453%nat))].
Hypothesis C_N1 : rw_cells asegs m (4096 * V 453%nat + 16) [C8 (wz h)].
Hypothesis C_N2 : rw_cells asegs m (4096 * V 453%nat + 24) [C4 (wz 0)].
Hypothesis C_N3 : rw_cells asegs m (4096 * V 453%nat + 28) [C4 (wz 1)].
Hypothesis Z_N : forall i, 0 <= i < 1048544 -> m (wa (4096 * V 453%nat + 32 + i)) = Some (Z_to_bv 8 0).
Hypothesis W_N : wr_at asegs m (4096 * V 453%nat) 1048576.
Hypothesis C_SSA : rw_cells asegs m SSA [C8 (wz tot)].
Hypothesis C_SSD1 : rw_cells asegs m SSD [C8 (wz (4096 * V 454%nat))].
Hypothesis C_SSD2 : rw_cells asegs m 1598496 [C4 (wz tot)].
Hypothesis Z_S : forall i, 0 <= i < 8388608 - 8 * tot -> m (wa (4096 * V 454%nat + 8 * tot + i)) = Some (Z_to_bv 8 0).
Hypothesis W_S : wr_at asegs m (4096 * V 454%nat) 8388608.

#[using="bk BK HR BKR TOT IMG1 IMG2 BW C_DNI C_DM1 C_N1 C_N2 C_N3 Z_N W_N C_SSA C_SSD1 C_SSD2 Z_S W_S"] Lemma RDEPOT_gen : RDEPOT (al_depot (AL_of V)) [h] tot m.
Proof.
  pose proof W_N as (WN0 & _). pose proof W_S as (WS0 & _).
  unfold RDEPOT, nodesrep, tabrep, AL_of. cbn [al_depot DN0 SS0 SWIN]. unfold zlen. cbn [length Z.of_nat Pos.of_succ_nat].
  split.
  {
    intros b Hb. unfold head_of. cbn [head_from]. rewrite BK. destruct (Z.eqb_spec bk b) as [<-|NE]; [exact BW|].
    change (2^20) with 1048576 in *.
    split; [split; [cbn; tauto|]| cbn [cells_size csize Nat.add]; apply b0_rw_image_wr_at; lia].
    cbn [cells_bytes cbytes]. rewrite app_nil_r.
    replace (le4 (wz 0)) with (repeat (Z_to_bv 8 0) 4) by (apply bytes_eq_unsigned; vm_compute; reflexivity).
    split; [lia|]. split; [rewrite repeat_length; change (2^64) with 18446744073709551616; lia|]. intros i Hi. rewrite repeat_length in Hi.
    rewrite nth_error_repeat by exact Hi. unfold mrd.
    assert (MN : m (wa (DT + 4 * b + Z.of_nat i)) = None).
    { destruct (Z_lt_le_dec b bk) as [LT|GE]; [apply IMG1; lia| apply IMG2; lia]. }
    rewrite MN. apply depot_tab_rom. lia. }
  split; [exact C_DNI|]. split; [exact C_DM1|].
  split.
  { intros i Hi. assert (i = 1) by lia. subst i. exists (wz 1). unfold hnth, lnk. cbn [Z.sub Z.to_nat nth firstn Z.add Z.opp Z.pos_sub Pos.to_nat Pos.iter_op].
    change (Z.to_nat (1 - 1)) with 0%nat. cbn [nth firstn]. unfold head_of. cbn [head_from].
    replace (4096 * V 453%nat + 16 * 1) with (4096 * V 453%nat + 16) by lia.
    apply (proj2 (rw_cells_app asegs m _ [_] [_; _])). split; [exact C_N1|]. cbn [cells_size csize Nat.add].
    replace (4096 * V 453%nat + 16 + Z.of_nat 8) with (4096 * V 453%nat + 24) by lia.
    apply (proj2 (rw_cells_app asegs m _ [_] [_])). split; [exact C_N2|]. cbn [cells_size csize Nat.add].
    replace (4096 * V 453%nat + 24 + Z.of_nat 4) with (4096 * V 453%nat + 28) by lia. exact C_N3. }
  split.
  { exists (repeat (Z_to_bv 8 0) (Z.to_nat (2^20 - 16 * (1 + 1)))).
    apply (zero_run m _ _ 1048544 _ 1048576 Z_N W_N 0 (2^20 - 16 * (1 + 1))); change (2^20) with 1048576; lia. }
  split; [exact C_SSA|].
  split.
  { apply (rw_cells_app2 m _ [_] _ 1598496 C_SSD1); [reflexivity| exact C_SSD2]. }
  split.
  { exists (repeat (Z_to_bv 8 0) (Z.to_nat (8388608 - 8 * tot))).
    apply (zero_run m _ _ (8388608 - 8 * tot) _ 8388608 Z_S W_S 0 (8388608 - 8 * tot)); lia. }
  split; [constructor; [exact HR| constructor]|]. change (2^20) with 1048576. repeat split; lia.
Qed.
End Gen.

#[using="Type"] Lemma RDEPOT_init : forall w, Forall (mfact_ok asegs V m) (both_mem_facts ++ both_mem_facts_w w) ->
  RDEPOT (al_depot (AL_of V)) [depot_h w] (depot_tot w) m.
Proof.
  intros w HM. unfold both_mem_facts_w in HM.
  mf V m HM (MCell (ZLit 5858328) 4 (ZLit 1)) C_DNI. mf V m HM (MCell (ZLit 5858344) 8 (ZMul (ZLit 4096) (ZV 453))) C_DM1.
  mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 453)) (ZLit 24)) 4 (ZLit 0)) C_N2. mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 453)) (ZLit 28)) 4 (ZLit 1)) C_N3.
  mf V m HM (MZero (ZAdd (ZMul (ZLit 4096) (ZV 453)) (ZLit 32)) 1048544) Z_N. mf V m HM (MWr (ZMul (ZLit 4096) (ZV 453)) 1048576) W_N.
  mf V m HM (MCell (ZLit 1598488) 8 (ZMul (ZLit 4096) (ZV 454))) C_SSD1. mf V m HM (MWr (ZMul (ZLit 4096) (ZV 454)) 8388608) W_S.
  destruct w; unfold depot_h, depot_tot.
  - mimg V m HM 1598504 5230696 I1. mimg V m HM 5230700 5858328 I2.
    mf V m HM (MCell (ZLit 5230696) 4 (ZLit 1)) BW.
    mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 453)) (ZLit 16)) 8 (ZLit 17443417135023758100)) C_N1.
    mf V m HM (MCell (ZLit 1598472) 8 (ZLit 3)) C_SSA. mf V m HM (MCell (ZLit 1598496) 4 (ZLit 3)) C_SSD2.
    mf V m HM (MZero (ZAdd (ZMul (ZLit 4096) (ZV 454)) (ZLit 24)) 8388584) Z_S.
    apply (RDEPOT_gen 17443417135023758100 891668 3); try assumption; try (vm_compute; reflexivity); try lia.
  - mimg V m HM 1598504 3188872 I1. mimg V m HM 3188876 5858328 I2.
    mf V m HM (MCell (ZLit 3188872) 4 (ZLit 1)) BW.
    mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 453)) (ZLit 16)) 8 (ZLit 13038664596505088284)) C_N1.
    mf V m HM (MCell (ZLit 1598472) 8 (ZLit 2)) C_SSA. mf V m HM (MCell (ZLit 1598496) 4 (ZLit 2)) C_SSD2.
    mf V m HM (MZero (ZAdd (ZMul (ZLit 4096) (ZV 454)) (ZLit 16)) 8388592) Z_S.
    apply (RDEPOT_gen 13038664596505088284 381212 2); try assumption; try (vm_compute; reflexivity); try lia.
Qed.

#[using="Type"] Lemma depot_side : forall w, List.NoDup [depot_h w] /\ 0 <= depot_tot w <= 31 * zlen [depot_h w] /\ (length [depot_h w] <= 4)%nat.
Proof. intros w. split; [constructor; [intros []| constructor]|]. split; [unfold zlen, depot_tot; cbn [length]; destruct w; lia| cbn [length]; lia]. Qed.
End Dep.
