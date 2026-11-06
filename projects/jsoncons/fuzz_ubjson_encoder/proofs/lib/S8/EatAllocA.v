(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import As0Tables.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import ArtMem ArtRegs ArtAtomics ArtTac EatLeaf EatRzLog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_r3cf10_3de98.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition art_alloc_rodata (M : word -> option byte) : Prop :=
  cellA M 0x10448 8 0x218a392cd3d5dbf /\ cellA M 0x104c4 1 3 /\ cellA M 0x10370 8 0xcc6e96b9cc6e96b9.

Definition art_alloc_memA1 (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
  (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 128 + 120) (U raw)) (sp - 128 + 112) (U (getr regs 8))) (sp - 128 + 104) (U (getr regs 9))) (sp - 128 + 96) (U (getr regs 18))) (sp - 128 + 88) (U (getr regs 19))) (sp - 128 + 80) (U (getr regs 20))) (sp - 128 + 72) (U (getr regs 21))) (sp - 128 + 64) (U (getr regs 22))) (sp - 128 + 56) (U (getr regs 23))) (sp - 128 + 48) (U (getr regs 24))) (sp - 128 + 40) (U (getr regs 25))) (sp - 128 + 32) (U (getr regs 26))) (sp - 128 + 24) (U (getr regs 27))) (sp - 128 + 8) 1) (sp - 128 + 16) 16).

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_alloc_a1_fn : forall regs (M rom : word -> option byte) (raw : word) (sp ia n stk : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 ia -> getr regs 11 = Z_to_bv 64 n ->
  getr regs 12 = Z_to_bv 64 8 -> getr regs 13 = Z_to_bv 64 stk -> getr regs 14 = Z_to_bv 64 1 -> getr regs 15 = Z_to_bv 64 1 ->
  256 <= sp -> sp < 2 ^ 64 -> 4096 <= ia -> ia + 4096 < 2 ^ 64 -> 1 <= stk < 2 ^ 64 -> 1 <= n < 2 ^ 40 ->
  wrA M (sp - 256) 256 -> 0x698000 + 256 <= sp ->
  art_alloc_rodata M -> cellA M 0x1426d8 1 1 -> cellA M 0x1c3c62 1 0 ->
  msteps ASEGS (mkst regs (0x52dcc : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x52e28 : bv 64)%bv) 2 (Z_to_bv 64 (sp - 128))) 8 (Z_to_bv 64 8)) 9 (Z_to_bv 64 1)) 10 (Z_to_bv 64 49)) 11 (Z_to_bv 64 16)) 12 (Z_to_bv 64 0x104c0)) 13 (Z_to_bv 64 (2 ^ 64 - 8))) 18 (Z_to_bv 64 8)) 21 (Z_to_bv 64 n)) 22 (Z_to_bv 64 ia)) 23 (Z_to_bv 64 stk)) 25 (Z_to_bv 64 7)) 26 (Z_to_bv 64 (ia + 2047))) 27 (Z_to_bv 64 1)) (0x52e64 : word) (art_alloc_memA1 M sp raw regs) rom).
Proof.
  intros regs M rom raw sp ia n stk H1 H2 H10 H11 H12 H13 H14 H15 Hsp Hsp' Hia Hia' Hstk Hn W IMG (R1 & R2 & R3) Ci Cr.
  zstep F_52d7c D_52d7c.
  zsd F_52d80 D_52d80 (sp - 128 + 120) (U raw) ltac:(rewok W).
  zsd F_52d84 D_52d84 (sp - 128 + 112) (U (getr regs 8)) ltac:(rewok W).
  zsd F_52d88 D_52d88 (sp - 128 + 104) (U (getr regs 9)) ltac:(rewok W).
  zsd F_52d8c D_52d8c (sp - 128 + 96) (U (getr regs 18)) ltac:(rewok W).
  zsd F_52d90 D_52d90 (sp - 128 + 88) (U (getr regs 19)) ltac:(rewok W).
  zsd F_52d94 D_52d94 (sp - 128 + 80) (U (getr regs 20)) ltac:(rewok W).
  zsd F_52d98 D_52d98 (sp - 128 + 72) (U (getr regs 21)) ltac:(rewok W).
  zsd F_52d9c D_52d9c (sp - 128 + 64) (U (getr regs 22)) ltac:(rewok W).
  zsd F_52da0 D_52da0 (sp - 128 + 56) (U (getr regs 23)) ltac:(rewok W).
  zsd F_52da4 D_52da4 (sp - 128 + 48) (U (getr regs 24)) ltac:(rewok W).
  zsd F_52da8 D_52da8 (sp - 128 + 40) (U (getr regs 25)) ltac:(rewok W).
  zsd F_52dac D_52dac (sp - 128 + 32) (U (getr regs 26)) ltac:(rewok W).
  zsd F_52db0 D_52db0 (sp - 128 + 24) (U (getr regs 27)) ltac:(rewok W).
  zstep F_52db4 D_52db4. zstep F_52db8 D_52db8. zstep F_52dbc D_52dbc. zstep F_52dc0 D_52dc0. zstep F_52dc4 D_52dc4. zstep F_52dc8 D_52dc8.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => set (Mf := X) end.
  assert (Ci' : cellA Mf 0x1426d8 1 1) by (unfold Mf; unfold apart in *; recell Ci).
  assert (Cr' : cellA Mf 0x1c3c62 1 0) by (unfold Mf; unfold apart in *; recell Cr).
  assert (R1' : cellA Mf 0x10448 8 0x218a392cd3d5dbf) by (unfold Mf; unfold apart in *; recell R1).
  assert (R2' : cellA Mf 0x104c4 1 3) by (unfold Mf; unfold apart in *; recell R2).
  stepn F_52dcc D_52dcc.
  zcall (art_asan_inited_fn _ _ _ _).
  zbft F_52dd0 D_52dd0.
  stepn F_52dd4 D_52dd4.
  zcall (art_rss_limit_fn _ _ _ _).
  zbft F_52dd8 D_52dd8.
  zbft F_52ddc D_52ddc.
  zstep F_52de0 D_52de0.
  zbtk F_52de4 D_52de4.
  zstep F_52e20 D_52e20. zstep F_52e24 D_52e24.
  zbtk F_52e28 D_52e28.
  zstep F_52e30 D_52e30. zstep F_52e34 D_52e34.
  zbft F_52e38 D_52e38.
  zstep F_52e3c D_52e3c. zld F_52e40 D_52e40 0x10448 R1'.
  zstep F_52e44 D_52e44. zstep F_52e48 D_52e48. zstep F_52e4c D_52e4c. zstep F_52e50 D_52e50. zstep F_52e54 D_52e54. zstep F_52e58 D_52e58.
  zstep F_52e5c D_52e5c.
  zlbu F_52e60 D_52e60 0x104c4 R2'.
  zstep F_52e64 D_52e64. zstep F_52e68 D_52e68. zstep F_52e6c D_52e6c. zstep F_52e70 D_52e70.
  zbtk F_52e74 D_52e74.
  zstep F_52df4 D_52df4. zstep F_52df8 D_52df8. zstep F_52dfc D_52dfc.
  zbft F_52e00 D_52e00.
  zstep F_52e04 D_52e04. zstep F_52e08 D_52e08.
  zsd F_52e0c D_52e0c (sp - 128 + 8) 1 ltac:(unfold Mf; rewok W).
  zsd F_52e10 D_52e10 (sp - 128 + 16) 16 ltac:(unfold Mf; rewok W).
  unfold Mf, art_alloc_memA1. zret.
Qed.

#[using="Type"] Lemma art_alloc_ladder : forall regs (M rom : word -> option byte) (n : Z),
  getr regs 10 = Z_to_bv 64 49 -> getr regs 21 = Z_to_bv 64 n -> 1 <= n < 2 ^ 40 ->
  exists regs',
    msteps ASEGS (mkst regs (0x52e64 : word) M rom) (mkst regs' (0x52f38 : word) M rom)
    /\ getr regs' 19 = Z_to_bv 64 (AsanTab.rz_log n)
    /\ (forall r : reg, r <> 10%bv -> r <> 19%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom n H10 H21 Hn.
  unfold AsanTab.rz_log.
  destruct (Z.le_gt_cases n 48) as [C0|C0'].
  { eexists. split; [|split]; [ zbft F_52e14 D_52e14; zstep F_52e18 D_52e18; stepn F_52e1c D_52e1c; apply mst_refl | gres; zif; reflexivity | intros; kept_solve ]. }
  destruct (Z.le_gt_cases n 96) as [C1|C1'].
  { eexists. split; [|split]; [ zbtk F_52e14 D_52e14; zstep F_52e7c D_52e7c; zbft F_52e80 D_52e80; zstep F_52e84 D_52e84; stepn F_52e88 D_52e88; apply mst_refl
    | gres; zif; reflexivity | intros; kept_solve ]. }
  destruct (Z.le_gt_cases n 448) as [C2|C2'].
  { eexists. split; [|split]; [ zbtk F_52e14 D_52e14; zstep F_52e7c D_52e7c; zbtk F_52e80 D_52e80; zstep F_52e8c D_52e8c; zbft F_52e90 D_52e90; zstep F_52e94 D_52e94;
      stepn F_52e98 D_52e98; apply mst_refl | gres; zif; reflexivity | intros; kept_solve ]. }
  destruct (Z.le_gt_cases n 3968) as [C3|C3'].
  { eexists. split; [|split]; [ zbtk F_52e14 D_52e14; zstep F_52e7c D_52e7c; zbtk F_52e80 D_52e80; zstep F_52e8c D_52e8c; zbtk F_52e90 D_52e90;
      zstep F_52e9c D_52e9c; zstep F_52ea0 D_52ea0; zbft F_52ea4 D_52ea4; zstep F_52ea8 D_52ea8; stepn F_52eac D_52eac; apply mst_refl
    | gres; zif; reflexivity | intros; kept_solve ]. }
  destruct (Z.le_gt_cases n 16128) as [C4|C4'].
  { eexists. split; [|split]; [ zbtk F_52e14 D_52e14; zstep F_52e7c D_52e7c; zbtk F_52e80 D_52e80; zstep F_52e8c D_52e8c; zbtk F_52e90 D_52e90;
      zstep F_52e9c D_52e9c; zstep F_52ea0 D_52ea0; zbtk F_52ea4 D_52ea4; zstep F_52eb0 D_52eb0; zstep F_52eb4 D_52eb4; zbft F_52eb8 D_52eb8;
      zstep F_52ebc D_52ebc; stepn F_52ec0 D_52ec0; apply mst_refl
    | gres; zif; reflexivity | intros; kept_solve ]. }
  destruct (Z.le_gt_cases n 32256) as [C5|C5'].
  { eexists. split; [|split]; [ zbtk F_52e14 D_52e14; zstep F_52e7c D_52e7c; zbtk F_52e80 D_52e80; zstep F_52e8c D_52e8c; zbtk F_52e90 D_52e90;
      zstep F_52e9c D_52e9c; zstep F_52ea0 D_52ea0; zbtk F_52ea4 D_52ea4; zstep F_52eb0 D_52eb0; zstep F_52eb4 D_52eb4; zbtk F_52eb8 D_52eb8;
      zstep F_52ec4 D_52ec4; zstep F_52ec8 D_52ec8; zbft F_52ecc D_52ecc; zstep F_52ed0 D_52ed0; stepn F_52ed4 D_52ed4; apply mst_refl
    | gres; zif; reflexivity | intros; kept_solve ]. }

  eexists. split; [|split]; [ zbtk F_52e14 D_52e14; zstep F_52e7c D_52e7c; zbtk F_52e80 D_52e80; zstep F_52e8c D_52e8c; zbtk F_52e90 D_52e90;
      zstep F_52e9c D_52e9c; zstep F_52ea0 D_52ea0; zbtk F_52ea4 D_52ea4; zstep F_52eb0 D_52eb0; zstep F_52eb4 D_52eb4; zbtk F_52eb8 D_52eb8;
      zstep F_52ec4 D_52ec4; zstep F_52ec8 D_52ec8; zbtk F_52ecc D_52ecc; zstep F_52ed8 D_52ed8; zstep F_52edc D_52edc; zstep F_52ee0 D_52ee0;
      zstep F_52ee4 D_52ee4; apply mst_refl
    | gres | intros; kept_solve ].
  destruct (Z.le_gt_cases n 64512) as [C6|C6']; zif; vals_lit; reflexivity.
Qed.

#[using="Type"] Lemma art_alloc_a2_fn : forall regs (M rom : word -> option byte) (sp ia : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 26 = Z_to_bv 64 (ia + 2047) ->
  16 <= sp -> sp < 2 ^ 64 -> 4096 <= ia -> ia + 4096 <= 0x698000 ->
  wrA M (sp - 16) 16 -> 0x698000 + 16 <= sp ->
  art_rz_rodata M -> cellA M (ia + 3624) 2 16 -> cellA M (ia + 3626) 2 2048 ->
  msteps ASEGS (mkst regs (0x52f38 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x52f64 : bv 64)%bv) 2 (Z_to_bv 64 sp)) 9 (Z_to_bv 64 0)) 10 (Z_to_bv 64 7)) 11 (Z_to_bv 64 7)) 12 (Z_to_bv 64 11)) 13 (Z_to_bv 64 2048)) 14 (Z_to_bv 64 2048)) 20 (Z_to_bv 64 65536)) 24 (Z_to_bv 64 65535)) (0x52f64 : word) (Wn 8 (Wn 8 M (sp - 8) 0x52f50) (sp - 8) 0x52f64) rom).
Proof.
  intros regs M rom sp ia H2 H26 Hsp Hsp' Hia Hia' W IMG RO Cmin Cmax.
  zlh F_52ee8 D_52ee8 (ia + 3624) Cmin.
  stepfence F_52eec D_52eec.
  zstep F_52ef0 D_52ef0. zstep F_52ef4 D_52ef4. zstep F_52ef8 D_52ef8.
  stepn F_52efc D_52efc.
  zcall (art_rz2log_16_fn _ _ _ sp _).
  zstep F_52f00 D_52f00.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cmax' : cellA X (ia + 3626) 2 2048) by (unfold apart in *; recell Cmax) end.
  zlh F_52f04 D_52f04 (ia + 3626) Cmax'.
  stepfence F_52f08 D_52f08.
  zstep F_52f0c D_52f0c.
  stepn F_52f10 D_52f10.
  zcall (art_rz2log_2048_fn _ _ _ sp _).
  { destruct RO as (R1 & R2 & R3). unfold art_rz_rodata. repeat split; recell R1 || recell R2 || recell R3. }
  zret.
Qed.

#[using="Type"] Lemma art_alloc_clamp : forall regs (M rom : word -> option byte) (n r : Z),
  getr regs 9 = Z_to_bv 64 0 -> getr regs 10 = Z_to_bv 64 7 -> getr regs 19 = Z_to_bv 64 r -> getr regs 21 = Z_to_bv 64 n ->
  1 <= n < 2 ^ 40 -> r = AsanTab.rz_log n ->
  exists regs',
    msteps ASEGS (mkst regs (0x52f64 : word) M rom) (mkst regs' (0x52f80 : word) M rom)
    /\ getr regs' 10 = Z_to_bv 64 (Z.max n 8) /\ getr regs' 11 = Z_to_bv 64 8 /\ getr regs' 19 = Z_to_bv 64 r
    /\ (forall x : reg, x <> 10%bv -> x <> 11%bv -> x <> 19%bv -> getr regs' x = getr regs x).
Proof.
  intros regs M rom n r H9 H10 H19 H21 Hn Hr.
  pose proof (AsanTab.rz_log_range n) as Rr. rewrite <- Hr in Rr.
  assert (CASES : r = 0 \/ (0 < r < 7) \/ r = 7) by lia.
  assert (Rlo : 0 < r -> 49 <= n).
  { intros Hp. destruct (Z.le_gt_cases n 48) as [L|G]; [exfalso|lia]. subst r. unfold AsanTab.rz_log in Hp.
    replace (n <=? 48) with true in Hp by (symmetry; apply Z.leb_le; lia). lia. }
  assert (R7 : r = 7 -> 64513 <= n).
  { intros Hp. destruct (Z.le_gt_cases n 64512) as [L|G]; [exfalso|lia]. subst r. unfold AsanTab.rz_log in Hp.
    repeat (lazymatch type of Hp with context [if ?c then _ else _] => destruct c eqn:?; [lia|] end).
    repeat match goal with H : (_ <=? _) = false |- _ => apply Z.leb_gt in H; revert H end. lia. }
  destruct CASES as [R0 | [RM | RS]].
  - destruct (Z.le_gt_cases n 8) as [S|B].
    + eexists. split; [|split; [|split; [|split]]];
        [ zbft F_52f14 D_52f14; zstep F_52f18 D_52f18; zbft F_52f1c D_52f1c; zstep F_52f20 D_52f20; zstep F_52f24 D_52f24; zbft F_52f28 D_52f28; zstep F_52f2c D_52f2c; apply mst_refl
        | gres; f_equal; lia | gres; reflexivity | gres; rwH; f_equal; lia | intros; kept_solve ].
    + eexists. split; [|split; [|split; [|split]]];
        [ zbft F_52f14 D_52f14; zstep F_52f18 D_52f18; zbft F_52f1c D_52f1c; zstep F_52f20 D_52f20; zstep F_52f24 D_52f24; zbtk F_52f28 D_52f28; apply mst_refl
        | gres; rwH; f_equal; lia | gres; reflexivity | gres; rwH; f_equal; lia | intros; kept_solve ].
  - specialize (Rlo ltac:(lia)).
    eexists. split; [|split; [|split; [|split]]];
      [ zbtk F_52f14 D_52f14; zbtk F_52fc0 D_52fc0; zstep F_52f20 D_52f20; zstep F_52f24 D_52f24; zbtk F_52f28 D_52f28; apply mst_refl
      | gres; rwH; f_equal; lia | gres; reflexivity | gres; rwH; reflexivity | intros; kept_solve ].
  - specialize (R7 RS).
    eexists. split; [|split; [|split; [|split]]];
      [ zbtk F_52f14 D_52f14; zbft F_52fc0 D_52fc0; zstep F_52fc4 D_52fc4; zstep F_52fc8 D_52fc8; zstep F_52fcc D_52fcc; zbft F_52fd0 D_52fd0;
        stepn F_52fd4 D_52fd4; apply mst_refl
      | gres; rwH; f_equal; lia | gres; reflexivity | gres; rwH; f_equal; lia | intros; kept_solve ].
Qed.

#[using="Type"] Lemma art_zb_sllw_small : forall x k, 0 <= x -> 0 <= k < 32 -> x * 2 ^ k < 2 ^ 31 ->
  v_sllw (Z_to_bv 64 x) (Z_to_bv 64 k) = Z_to_bv 64 (x * 2 ^ k).
Proof.
  intros x k Hx Hk Hxk. unfold v_sllw.
  assert (Hx' : x < 2 ^ 31). { pose proof (Z.pow_pos_nonneg 2 k). nia. }
  rewrite !art_u_lit by lia. rewrite Z.mod_small by lia. rewrite Z.shiftl_mul_pow2 by lia. f_equal.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  pose proof (Z.pow_pos_nonneg 2 k). rewrite Z.mod_small by nia. lia.
Qed.

#[using="Type"] Lemma art_alloc_a3_fn : forall regs (M rom : word -> option byte) (sp ia n r rs rz tp key tsd ctx t : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> getr regs 8 = Z_to_bv 64 8 -> getr regs 10 = Z_to_bv 64 (Z.max n 8) ->
  getr regs 18 = Z_to_bv 64 8 -> getr regs 19 = Z_to_bv 64 r -> getr regs 20 = Z_to_bv 64 65536 -> getr regs 21 = Z_to_bv 64 n ->
  getr regs 22 = Z_to_bv 64 ia -> getr regs 26 = Z_to_bv 64 (ia + 2047) ->
  16 <= sp -> sp < 2 ^ 64 -> 4096 <= ia -> ia + 4096 <= 0x698000 -> 0x698000 + 16 <= sp ->
  1 <= n < 2 ^ 40 -> 0 <= r <= 7 -> rs = (Z.max n 8 + 7) / 8 * 8 -> rz = 16 * 2 ^ r -> rs + rz <= 65536 ->
  wrA M (sp - 16) 16 -> cellA M (ia + 3616) 8 (2 ^ 40) -> art_tsd M tp key tsd ctx t -> 1 <= t ->
  apart (sp - 16) 16 (tp - 88) 8 -> apart (sp - 16) 16 (tsd + 8 * key) 8 -> apart (sp - 16) 16 (ctx + 152) 8 ->
  msteps ASEGS (mkst regs (0x52f80 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x5306c : bv 64)%bv) 2 (Z_to_bv 64 sp)) 8 (Z_to_bv 64 1)) 9 (Z_to_bv 64 n)) 10 (Z_to_bv 64 ia)) 11 (Z_to_bv 64 (t + 208))) 12 (Z_to_bv 64 (rs + rz))) 13 (Z_to_bv 64 8)) 19 (Z_to_bv 64 (rs + rz))) 20 (Z_to_bv 64 rz)) 24 (Z_to_bv 64 (2 ^ 64 - 8))) 26 (Z_to_bv 64 t)) (0x57524 : word) (Wn 8 M (sp - 8) 0x53050) rom).
Proof.
  intros regs M rom sp ia n r rs rz tp key tsd ctx t H2 H4 H8 H10 H18 H19 H20 H21 H22 H26 Hsp Hsp' Hia Hia' IMG Hn Hr Hrs Hrz Hprim W Cmax TSD Ht A1 A2 A3.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  assert (Hrs8 : rs mod 8 = 0) by (subst rs; apply Z_mod_mult).
  assert (Hrslo : 8 <= rs). { subst rs. pose proof (Z.mul_succ_div_gt (Z.max n 8 + 7) 8 ltac:(lia)). pose proof (Z.mul_div_le (Z.max n 8 + 7) 8 ltac:(lia)). lia. } assert (Hrz16 : 16 <= rz <= 2048) by (subst rz; split; [|change 2048 with (16 * 2 ^ 7); apply Z.mul_le_mono_nonneg_l; [lia|apply Z.pow_le_mono_r; lia]]; pose proof (Z.pow_pos_nonneg 2 r); nia).
  zstep F_52f30 D_52f30. zstep F_52f34 D_52f34. zstep F_52f38 D_52f38. zstep F_52f3c D_52f3c. zstep F_52f40 D_52f40.
  stepn F_52f44 D_52f44. rwH. rewrite art_zb_and by lia. rewrite art_land_m8 by lia.
  match goal with |- context [Z_to_bv 64 (?e / 8 * 8)] => replace (e / 8 * 8) with rs by (rewrite Hrs; f_equal; f_equal; lia) end.
  zstep F_52f48 D_52f48. zstep F_52f4c D_52f4c.
  stepn F_52f50 D_52f50. rwH. rewrite art_zb_andi by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8. rewrite Hrs8.
  zbft F_52f54 D_52f54.
  zstep F_52f58 D_52f58. zstep F_52f5c D_52f5c. zstep F_52f60 D_52f60.
  stepn F_52f64 D_52f64. rwH. rewrite art_zb_sllw_small by (subst rz; lia). rewrite <- Hrz.
  zstep F_52f68 D_52f68. zstep F_52f6c D_52f6c. zstep F_52f70 D_52f70. zstep F_52f74 D_52f74. zstep F_52f78 D_52f78. zstep F_52f7c D_52f7c.
  zstep F_52f80 D_52f80.
  stepn F_52f84 D_52f84. rwH. rewrite art_zb_and by lia. rewrite Z.land_0_l.
  zstep F_52f88 D_52f88. zstep F_52f8c D_52f8c.
  zbft F_52f90 D_52f90. zbft F_52f94 D_52f94.
  zld F_52f98 D_52f98 (ia + 3616) Cmax.
  zbtk F_52f9c D_52f9c.
  stepn F_52ffc D_52ffc.
  zcall (art_cur_thread_fn _ _ _ _ sp tp key tsd ctx t).
  zbft F_53004 D_53004 || (zstep F_53000 D_53000; zbft F_53004 D_53004).
  zstep F_53008 D_53008. zstep F_5300c D_5300c. zstep F_53010 D_53010. zstep F_53014 D_53014.
  stepn F_53018 D_53018.
  zret.
Qed.
End FPX.
