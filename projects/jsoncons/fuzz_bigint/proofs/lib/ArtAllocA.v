(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac ArtLeaf ArtRzLog.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import As0_code_3d034_3dfbc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Definition art_alloc_rodata (M : word -> option byte) : Prop :=
  cellA M 0x103e8 8 0x218a392cd3d5dbf /\ cellA M 0x1045c 1 3 /\ cellA M 0x10340 8 0xcc6e96b9cc6e96b9.

(* [comment removed for export] *)
Definition art_alloc_memA1 (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
  (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 128 + 120) (U raw)) (sp - 128 + 112) (U (getr regs 8))) (sp - 128 + 104) (U (getr regs 9))) (sp - 128 + 96) (U (getr regs 18))) (sp - 128 + 88) (U (getr regs 19))) (sp - 128 + 80) (U (getr regs 20))) (sp - 128 + 72) (U (getr regs 21))) (sp - 128 + 64) (U (getr regs 22))) (sp - 128 + 56) (U (getr regs 23))) (sp - 128 + 48) (U (getr regs 24))) (sp - 128 + 40) (U (getr regs 25))) (sp - 128 + 32) (U (getr regs 26))) (sp - 128 + 24) (U (getr regs 27))) (sp - 128 + 8) 1) (sp - 128 + 16) 16).

Section FPX. Context {fx : PropExec.FPState}.

Lemma art_alloc_a1_fn : forall regs (M rom : word -> option byte) (raw : word) (sp ia n stk : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 ia -> getr regs 11 = Z_to_bv 64 n ->
  getr regs 12 = Z_to_bv 64 8 -> getr regs 13 = Z_to_bv 64 stk -> getr regs 14 = Z_to_bv 64 1 -> getr regs 15 = Z_to_bv 64 1 ->
  256 <= sp -> sp < 2 ^ 64 -> 4096 <= ia -> ia + 4096 < 2 ^ 64 -> 1 <= stk < 2 ^ 64 -> 1 <= n < 2 ^ 40 ->
  wrA M (sp - 256) 256 -> 0x633000 + 256 <= sp ->
  art_alloc_rodata M -> cellA M 0xde818 1 1 -> cellA M 0x15fda2 1 0 ->
  msteps ASEGS (mkst regs (0x3d370 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x3d3cc : bv 64)%bv) 2 (Z_to_bv 64 (sp - 128))) 8 (Z_to_bv 64 8)) 9 (Z_to_bv 64 1)) 10 (Z_to_bv 64 49)) 11 (Z_to_bv 64 16)) 12 (Z_to_bv 64 0x10458)) 13 (Z_to_bv 64 (2 ^ 64 - 8))) 18 (Z_to_bv 64 8)) 21 (Z_to_bv 64 n)) 22 (Z_to_bv 64 ia)) 23 (Z_to_bv 64 stk)) 25 (Z_to_bv 64 7)) 26 (Z_to_bv 64 (ia + 2047))) 27 (Z_to_bv 64 1)) (0x3d408 : word) (art_alloc_memA1 M sp raw regs) rom).
Proof.
  intros regs M rom raw sp ia n stk H1 H2 H10 H11 H12 H13 H14 H15 Hsp Hsp' Hia Hia' Hstk Hn W IMG (R1 & R2 & R3) Ci Cr.
  zstep F_3d370 D_3d370.
  zsd F_3d374 D_3d374 (sp - 128 + 120) (U raw) ltac:(rewok W).
  zsd F_3d378 D_3d378 (sp - 128 + 112) (U (getr regs 8)) ltac:(rewok W).
  zsd F_3d37c D_3d37c (sp - 128 + 104) (U (getr regs 9)) ltac:(rewok W).
  zsd F_3d380 D_3d380 (sp - 128 + 96) (U (getr regs 18)) ltac:(rewok W).
  zsd F_3d384 D_3d384 (sp - 128 + 88) (U (getr regs 19)) ltac:(rewok W).
  zsd F_3d388 D_3d388 (sp - 128 + 80) (U (getr regs 20)) ltac:(rewok W).
  zsd F_3d38c D_3d38c (sp - 128 + 72) (U (getr regs 21)) ltac:(rewok W).
  zsd F_3d390 D_3d390 (sp - 128 + 64) (U (getr regs 22)) ltac:(rewok W).
  zsd F_3d394 D_3d394 (sp - 128 + 56) (U (getr regs 23)) ltac:(rewok W).
  zsd F_3d398 D_3d398 (sp - 128 + 48) (U (getr regs 24)) ltac:(rewok W).
  zsd F_3d39c D_3d39c (sp - 128 + 40) (U (getr regs 25)) ltac:(rewok W).
  zsd F_3d3a0 D_3d3a0 (sp - 128 + 32) (U (getr regs 26)) ltac:(rewok W).
  zsd F_3d3a4 D_3d3a4 (sp - 128 + 24) (U (getr regs 27)) ltac:(rewok W).
  zstep F_3d3a8 D_3d3a8. zstep F_3d3ac D_3d3ac. zstep F_3d3b0 D_3d3b0. zstep F_3d3b4 D_3d3b4. zstep F_3d3b8 D_3d3b8. zstep F_3d3bc D_3d3bc.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => set (Mf := X) end.
  assert (Ci' : cellA Mf 0xde818 1 1) by (unfold Mf; unfold apart in *; recell Ci).
  assert (Cr' : cellA Mf 0x15fda2 1 0) by (unfold Mf; unfold apart in *; recell Cr).
  assert (R1' : cellA Mf 0x103e8 8 0x218a392cd3d5dbf) by (unfold Mf; unfold apart in *; recell R1).
  assert (R2' : cellA Mf 0x1045c 1 3) by (unfold Mf; unfold apart in *; recell R2).
  stepn F_3d3c0 D_3d3c0.
  zcall (art_asan_inited_fn _ _ _ _).
  zbft F_3d3c4 D_3d3c4.
  stepn F_3d3c8 D_3d3c8.
  zcall (art_rss_limit_fn _ _ _ _).
  zbft F_3d3cc D_3d3cc.
  zbft F_3d3d0 D_3d3d0.
  zstep F_3d3d4 D_3d3d4.
  zbtk F_3d3d8 D_3d3d8.
  zstep F_3d414 D_3d414. zstep F_3d418 D_3d418.
  zbtk F_3d41c D_3d41c.
  zstep F_3d424 D_3d424. zstep F_3d428 D_3d428.
  zbft F_3d42c D_3d42c.
  zstep F_3d430 D_3d430. zld F_3d434 D_3d434 0x103e8 R1'.
  zstep F_3d438 D_3d438. zstep F_3d43c D_3d43c. zstep F_3d440 D_3d440. zstep F_3d444 D_3d444. zstep F_3d448 D_3d448. zstep F_3d44c D_3d44c.
  zstep F_3d450 D_3d450.
  zlbu F_3d454 D_3d454 0x1045c R2'.
  zstep F_3d458 D_3d458. zstep F_3d45c D_3d45c. zstep F_3d460 D_3d460. zstep F_3d464 D_3d464.
  zbtk F_3d468 D_3d468.
  zstep F_3d3e8 D_3d3e8. zstep F_3d3ec D_3d3ec. zstep F_3d3f0 D_3d3f0.
  zbft F_3d3f4 D_3d3f4.
  zstep F_3d3f8 D_3d3f8. zstep F_3d3fc D_3d3fc.
  zsd F_3d400 D_3d400 (sp - 128 + 8) 1 ltac:(unfold Mf; rewok W).
  zsd F_3d404 D_3d404 (sp - 128 + 16) 16 ltac:(unfold Mf; rewok W).
  unfold Mf, art_alloc_memA1. zret.
Qed.

(* [comment removed for export] *)
Lemma art_alloc_ladder : forall regs (M rom : word -> option byte) (n : Z),
  getr regs 10 = Z_to_bv 64 49 -> getr regs 21 = Z_to_bv 64 n -> 1 <= n < 2 ^ 40 ->
  exists regs',
    msteps ASEGS (mkst regs (0x3d408 : word) M rom) (mkst regs' (0x3d4dc : word) M rom)
    /\ getr regs' 19 = Z_to_bv 64 (AsanTab.rz_log n)
    /\ (forall r : reg, r <> 10%bv -> r <> 19%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom n H10 H21 Hn.
  unfold AsanTab.rz_log.
  destruct (Z.le_gt_cases n 48) as [C0|C0'].
  { eexists. split; [|split]; [ zbft F_3d408 D_3d408; zstep F_3d40c D_3d40c; stepn F_3d410 D_3d410; apply mst_refl | gres; zif; reflexivity | intros; kept_solve ]. }
  destruct (Z.le_gt_cases n 96) as [C1|C1'].
  { eexists. split; [|split]; [ zbtk F_3d408 D_3d408; zstep F_3d470 D_3d470; zbft F_3d474 D_3d474; zstep F_3d478 D_3d478; stepn F_3d47c D_3d47c; apply mst_refl
    | gres; zif; reflexivity | intros; kept_solve ]. }
  destruct (Z.le_gt_cases n 448) as [C2|C2'].
  { eexists. split; [|split]; [ zbtk F_3d408 D_3d408; zstep F_3d470 D_3d470; zbtk F_3d474 D_3d474; zstep F_3d480 D_3d480; zbft F_3d484 D_3d484; zstep F_3d488 D_3d488;
      stepn F_3d48c D_3d48c; apply mst_refl | gres; zif; reflexivity | intros; kept_solve ]. }
  destruct (Z.le_gt_cases n 3968) as [C3|C3'].
  { eexists. split; [|split]; [ zbtk F_3d408 D_3d408; zstep F_3d470 D_3d470; zbtk F_3d474 D_3d474; zstep F_3d480 D_3d480; zbtk F_3d484 D_3d484;
      zstep F_3d490 D_3d490; zstep F_3d494 D_3d494; zbft F_3d498 D_3d498; zstep F_3d49c D_3d49c; stepn F_3d4a0 D_3d4a0; apply mst_refl
    | gres; zif; reflexivity | intros; kept_solve ]. }
  destruct (Z.le_gt_cases n 16128) as [C4|C4'].
  { eexists. split; [|split]; [ zbtk F_3d408 D_3d408; zstep F_3d470 D_3d470; zbtk F_3d474 D_3d474; zstep F_3d480 D_3d480; zbtk F_3d484 D_3d484;
      zstep F_3d490 D_3d490; zstep F_3d494 D_3d494; zbtk F_3d498 D_3d498; zstep F_3d4a4 D_3d4a4; zstep F_3d4a8 D_3d4a8; zbft F_3d4ac D_3d4ac;
      zstep F_3d4b0 D_3d4b0; stepn F_3d4b4 D_3d4b4; apply mst_refl
    | gres; zif; reflexivity | intros; kept_solve ]. }
  destruct (Z.le_gt_cases n 32256) as [C5|C5'].
  { eexists. split; [|split]; [ zbtk F_3d408 D_3d408; zstep F_3d470 D_3d470; zbtk F_3d474 D_3d474; zstep F_3d480 D_3d480; zbtk F_3d484 D_3d484;
      zstep F_3d490 D_3d490; zstep F_3d494 D_3d494; zbtk F_3d498 D_3d498; zstep F_3d4a4 D_3d4a4; zstep F_3d4a8 D_3d4a8; zbtk F_3d4ac D_3d4ac;
      zstep F_3d4b8 D_3d4b8; zstep F_3d4bc D_3d4bc; zbft F_3d4c0 D_3d4c0; zstep F_3d4c4 D_3d4c4; stepn F_3d4c8 D_3d4c8; apply mst_refl
    | gres; zif; reflexivity | intros; kept_solve ]. }
  (* [comment removed for export] *)
  eexists. split; [|split]; [ zbtk F_3d408 D_3d408; zstep F_3d470 D_3d470; zbtk F_3d474 D_3d474; zstep F_3d480 D_3d480; zbtk F_3d484 D_3d484;
      zstep F_3d490 D_3d490; zstep F_3d494 D_3d494; zbtk F_3d498 D_3d498; zstep F_3d4a4 D_3d4a4; zstep F_3d4a8 D_3d4a8; zbtk F_3d4ac D_3d4ac;
      zstep F_3d4b8 D_3d4b8; zstep F_3d4bc D_3d4bc; zbtk F_3d4c0 D_3d4c0; zstep F_3d4cc D_3d4cc; zstep F_3d4d0 D_3d4d0; zstep F_3d4d4 D_3d4d4;
      zstep F_3d4d8 D_3d4d8; apply mst_refl
    | gres | intros; kept_solve ].
  destruct (Z.le_gt_cases n 64512) as [C6|C6']; zif; vals_lit; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma art_alloc_a2_fn : forall regs (M rom : word -> option byte) (sp ia : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 26 = Z_to_bv 64 (ia + 2047) ->
  16 <= sp -> sp < 2 ^ 64 -> 4096 <= ia -> ia + 4096 <= 0x633000 ->
  wrA M (sp - 16) 16 -> 0x633000 + 16 <= sp ->
  art_rz_rodata M -> cellA M (ia + 3624) 2 16 -> cellA M (ia + 3626) 2 2048 ->
  msteps ASEGS (mkst regs (0x3d4dc : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x3d508 : bv 64)%bv) 2 (Z_to_bv 64 sp)) 9 (Z_to_bv 64 0)) 10 (Z_to_bv 64 7)) 11 (Z_to_bv 64 7)) 12 (Z_to_bv 64 11)) 13 (Z_to_bv 64 2048)) 14 (Z_to_bv 64 2048)) 20 (Z_to_bv 64 65536)) 24 (Z_to_bv 64 65535)) (0x3d508 : word) (Wn 8 (Wn 8 M (sp - 8) 0x3d4f4) (sp - 8) 0x3d508) rom).
Proof.
  intros regs M rom sp ia H2 H26 Hsp Hsp' Hia Hia' W IMG RO Cmin Cmax.
  zlh F_3d4dc D_3d4dc (ia + 3624) Cmin.
  stepfence F_3d4e0 D_3d4e0.
  zstep F_3d4e4 D_3d4e4. zstep F_3d4e8 D_3d4e8. zstep F_3d4ec D_3d4ec.
  stepn F_3d4f0 D_3d4f0.
  zcall (art_rz2log_16_fn _ _ _ sp _).
  zstep F_3d4f4 D_3d4f4.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cmax' : cellA X (ia + 3626) 2 2048) by (unfold apart in *; recell Cmax) end.
  zlh F_3d4f8 D_3d4f8 (ia + 3626) Cmax'.
  stepfence F_3d4fc D_3d4fc.
  zstep F_3d500 D_3d500.
  stepn F_3d504 D_3d504.
  zcall (art_rz2log_2048_fn _ _ _ sp _).
  { destruct RO as (R1 & R2 & R3). unfold art_rz_rodata. repeat split; recell R1 || recell R2 || recell R3. }
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_alloc_clamp : forall regs (M rom : word -> option byte) (n r : Z),
  getr regs 9 = Z_to_bv 64 0 -> getr regs 10 = Z_to_bv 64 7 -> getr regs 19 = Z_to_bv 64 r -> getr regs 21 = Z_to_bv 64 n ->
  1 <= n < 2 ^ 40 -> r = AsanTab.rz_log n ->
  exists regs',
    msteps ASEGS (mkst regs (0x3d508 : word) M rom) (mkst regs' (0x3d524 : word) M rom)
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
        [ zbft F_3d508 D_3d508; zstep F_3d50c D_3d50c; zbft F_3d510 D_3d510; zstep F_3d514 D_3d514; zstep F_3d518 D_3d518; zbft F_3d51c D_3d51c; zstep F_3d520 D_3d520; apply mst_refl
        | gres; f_equal; lia | gres; reflexivity | gres; rwH; f_equal; lia | intros; kept_solve ].
    + eexists. split; [|split; [|split; [|split]]];
        [ zbft F_3d508 D_3d508; zstep F_3d50c D_3d50c; zbft F_3d510 D_3d510; zstep F_3d514 D_3d514; zstep F_3d518 D_3d518; zbtk F_3d51c D_3d51c; apply mst_refl
        | gres; rwH; f_equal; lia | gres; reflexivity | gres; rwH; f_equal; lia | intros; kept_solve ].
  - specialize (Rlo ltac:(lia)).
    eexists. split; [|split; [|split; [|split]]];
      [ zbtk F_3d508 D_3d508; zbtk F_3d5b4 D_3d5b4; zstep F_3d514 D_3d514; zstep F_3d518 D_3d518; zbtk F_3d51c D_3d51c; apply mst_refl
      | gres; rwH; f_equal; lia | gres; reflexivity | gres; rwH; reflexivity | intros; kept_solve ].
  - specialize (R7 RS).
    eexists. split; [|split; [|split; [|split]]];
      [ zbtk F_3d508 D_3d508; zbft F_3d5b4 D_3d5b4; zstep F_3d5b8 D_3d5b8; zstep F_3d5bc D_3d5bc; zstep F_3d5c0 D_3d5c0; zbft F_3d5c4 D_3d5c4;
        stepn F_3d5c8 D_3d5c8; apply mst_refl
      | gres; rwH; f_equal; lia | gres; reflexivity | gres; rwH; f_equal; lia | intros; kept_solve ].
Qed.

Lemma art_zb_sllw_small : forall x k, 0 <= x -> 0 <= k < 32 -> x * 2 ^ k < 2 ^ 31 ->
  v_sllw (Z_to_bv 64 x) (Z_to_bv 64 k) = Z_to_bv 64 (x * 2 ^ k).
Proof.
  intros x k Hx Hk Hxk. unfold v_sllw.
  assert (Hx' : x < 2 ^ 31). { pose proof (Z.pow_pos_nonneg 2 k). nia. }
  rewrite !art_u_lit by lia. rewrite Z.mod_small by lia. rewrite Z.shiftl_mul_pow2 by lia. f_equal.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  pose proof (Z.pow_pos_nonneg 2 k). rewrite Z.mod_small by nia. lia.
Qed.

(* [comment removed for export] *)
Lemma art_alloc_a3_fn : forall regs (M rom : word -> option byte) (sp ia n r rs rz tp key tsd ctx t : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> getr regs 8 = Z_to_bv 64 8 -> getr regs 10 = Z_to_bv 64 (Z.max n 8) ->
  getr regs 18 = Z_to_bv 64 8 -> getr regs 19 = Z_to_bv 64 r -> getr regs 20 = Z_to_bv 64 65536 -> getr regs 21 = Z_to_bv 64 n ->
  getr regs 22 = Z_to_bv 64 ia -> getr regs 26 = Z_to_bv 64 (ia + 2047) ->
  16 <= sp -> sp < 2 ^ 64 -> 4096 <= ia -> ia + 4096 <= 0x633000 -> 0x633000 + 16 <= sp ->
  1 <= n < 2 ^ 40 -> 0 <= r <= 7 -> rs = (Z.max n 8 + 7) / 8 * 8 -> rz = 16 * 2 ^ r -> rs + rz <= 65536 ->
  wrA M (sp - 16) 16 -> cellA M (ia + 3616) 8 (2 ^ 40) -> art_tsd M tp key tsd ctx t -> 1 <= t ->
  apart (sp - 16) 16 (tp - 88) 8 -> apart (sp - 16) 16 (tsd + 8 * key) 8 -> apart (sp - 16) 16 (ctx + 152) 8 ->
  msteps ASEGS (mkst regs (0x3d524 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x3d610 : bv 64)%bv) 2 (Z_to_bv 64 sp)) 8 (Z_to_bv 64 1)) 9 (Z_to_bv 64 n)) 10 (Z_to_bv 64 ia)) 11 (Z_to_bv 64 (t + 208))) 12 (Z_to_bv 64 (rs + rz))) 13 (Z_to_bv 64 8)) 19 (Z_to_bv 64 (rs + rz))) 20 (Z_to_bv 64 rz)) 24 (Z_to_bv 64 (2 ^ 64 - 8))) 26 (Z_to_bv 64 t)) (0x41ac8 : word) (Wn 8 M (sp - 8) 0x3d5f4) rom).
Proof.
  intros regs M rom sp ia n r rs rz tp key tsd ctx t H2 H4 H8 H10 H18 H19 H20 H21 H22 H26 Hsp Hsp' Hia Hia' IMG Hn Hr Hrs Hrz Hprim W Cmax TSD Ht A1 A2 A3.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  assert (Hrs8 : rs mod 8 = 0) by (subst rs; apply Z_mod_mult).
  assert (Hrslo : 8 <= rs). { subst rs. pose proof (Z.mul_succ_div_gt (Z.max n 8 + 7) 8 ltac:(lia)). pose proof (Z.mul_div_le (Z.max n 8 + 7) 8 ltac:(lia)). lia. } assert (Hrz16 : 16 <= rz <= 2048) by (subst rz; split; [|change 2048 with (16 * 2 ^ 7); apply Z.mul_le_mono_nonneg_l; [lia|apply Z.pow_le_mono_r; lia]]; pose proof (Z.pow_pos_nonneg 2 r); nia).
  zstep F_3d524 D_3d524. zstep F_3d528 D_3d528. zstep F_3d52c D_3d52c. zstep F_3d530 D_3d530. zstep F_3d534 D_3d534.
  stepn F_3d538 D_3d538. rwH. rewrite art_zb_and by lia. rewrite art_land_m8 by lia.
  match goal with |- context [Z_to_bv 64 (?e / 8 * 8)] => replace (e / 8 * 8) with rs by (rewrite Hrs; f_equal; f_equal; lia) end.
  zstep F_3d53c D_3d53c. zstep F_3d540 D_3d540.
  stepn F_3d544 D_3d544. rwH. rewrite art_zb_andi by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8. rewrite Hrs8.
  zbft F_3d548 D_3d548.
  zstep F_3d54c D_3d54c. zstep F_3d550 D_3d550. zstep F_3d554 D_3d554.
  stepn F_3d558 D_3d558. rwH. rewrite art_zb_sllw_small by (subst rz; lia). rewrite <- Hrz.
  zstep F_3d55c D_3d55c. zstep F_3d560 D_3d560. zstep F_3d564 D_3d564. zstep F_3d568 D_3d568. zstep F_3d56c D_3d56c. zstep F_3d570 D_3d570.
  zstep F_3d574 D_3d574.
  stepn F_3d578 D_3d578. rwH. rewrite art_zb_and by lia. rewrite Z.land_0_l.
  zstep F_3d57c D_3d57c. zstep F_3d580 D_3d580.
  zbft F_3d584 D_3d584. zbft F_3d588 D_3d588.
  zld F_3d58c D_3d58c (ia + 3616) Cmax.
  zbtk F_3d590 D_3d590.
  stepn F_3d5f0 D_3d5f0.
  zcall (art_cur_thread_fn _ _ _ _ sp tp key tsd ctx t).
  zbft F_3d5f8 D_3d5f8 || (zstep F_3d5f4 D_3d5f4; zbft F_3d5f8 D_3d5f8).
  zstep F_3d5fc D_3d5fc. zstep F_3d600 D_3d600. zstep F_3d604 D_3d604. zstep F_3d608 D_3d608.
  stepn F_3d60c D_3d60c.
  zret.
Qed.
End FPX.
