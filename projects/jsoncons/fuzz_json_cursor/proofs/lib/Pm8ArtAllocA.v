(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac Pm8ArtLeaf Pm8ArtRzLog.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm8_code_59000_5a000 .
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition art_alloc_rodata (M : word -> option byte) : Prop :=
  cellA M 0x10460 8 0x218a392cd3d5dbf /\ cellA M 0x104dc 1 3 /\ cellA M 0x10378 8 0xcc6e96b9cc6e96b9.

Definition art_alloc_memA1 (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
  (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 128 + 120) (U raw)) (sp - 128 + 112) (U (getr regs 8))) (sp - 128 + 104) (U (getr regs 9))) (sp - 128 + 96) (U (getr regs 18))) (sp - 128 + 88) (U (getr regs 19))) (sp - 128 + 80) (U (getr regs 20))) (sp - 128 + 72) (U (getr regs 21))) (sp - 128 + 64) (U (getr regs 22))) (sp - 128 + 56) (U (getr regs 23))) (sp - 128 + 48) (U (getr regs 24))) (sp - 128 + 40) (U (getr regs 25))) (sp - 128 + 32) (U (getr regs 26))) (sp - 128 + 24) (U (getr regs 27))) (sp - 128 + 8) 1) (sp - 128 + 16) 16).

Section FPX. Context {fx : PropExec.FPState}.

Lemma art_alloc_a1_fn : forall regs (M rom : word -> option byte) (raw : word) (sp ia n stk : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 ia -> getr regs 11 = Z_to_bv 64 n ->
  getr regs 12 = Z_to_bv 64 8 -> getr regs 13 = Z_to_bv 64 stk -> getr regs 14 = Z_to_bv 64 1 -> getr regs 15 = Z_to_bv 64 1 ->
  256 <= sp -> sp < 2 ^ 64 -> 4096 <= ia -> ia + 4096 < 2 ^ 64 -> 1 <= stk < 2 ^ 64 -> 1 <= n < 2 ^ 40 ->
  wrA M (sp - 256) 256 -> 0x6b3000 + 256 <= sp ->
  art_alloc_rodata M -> cellA M 0x15d698 1 1 -> cellA M 0x1dec22 1 0 ->
  msteps ASEGS (mkst regs (0x5945c : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x594b8 : bv 64)%bv) 2 (Z_to_bv 64 (sp - 128))) 8 (Z_to_bv 64 8)) 9 (Z_to_bv 64 1)) 10 (Z_to_bv 64 49)) 11 (Z_to_bv 64 16)) 12 (Z_to_bv 64 0x104d8)) 13 (Z_to_bv 64 (2 ^ 64 - 8))) 18 (Z_to_bv 64 8)) 21 (Z_to_bv 64 n)) 22 (Z_to_bv 64 ia)) 23 (Z_to_bv 64 stk)) 25 (Z_to_bv 64 7)) 26 (Z_to_bv 64 (ia + 2047))) 27 (Z_to_bv 64 1)) (0x594f4 : word) (art_alloc_memA1 M sp raw regs) rom).
Proof.
  intros regs M rom raw sp ia n stk H1 H2 H10 H11 H12 H13 H14 H15 Hsp Hsp' Hia Hia' Hstk Hn W IMG (R1 & R2 & R3) Ci Cr.
  zstep F_5940c D_5940c.
  zsd F_59410 D_59410 (sp - 128 + 120) (U raw) ltac:(rewok W).
  zsd F_59414 D_59414 (sp - 128 + 112) (U (getr regs 8)) ltac:(rewok W).
  zsd F_59418 D_59418 (sp - 128 + 104) (U (getr regs 9)) ltac:(rewok W).
  zsd F_5941c D_5941c (sp - 128 + 96) (U (getr regs 18)) ltac:(rewok W).
  zsd F_59420 D_59420 (sp - 128 + 88) (U (getr regs 19)) ltac:(rewok W).
  zsd F_59424 D_59424 (sp - 128 + 80) (U (getr regs 20)) ltac:(rewok W).
  zsd F_59428 D_59428 (sp - 128 + 72) (U (getr regs 21)) ltac:(rewok W).
  zsd F_5942c D_5942c (sp - 128 + 64) (U (getr regs 22)) ltac:(rewok W).
  zsd F_59430 D_59430 (sp - 128 + 56) (U (getr regs 23)) ltac:(rewok W).
  zsd F_59434 D_59434 (sp - 128 + 48) (U (getr regs 24)) ltac:(rewok W).
  zsd F_59438 D_59438 (sp - 128 + 40) (U (getr regs 25)) ltac:(rewok W).
  zsd F_5943c D_5943c (sp - 128 + 32) (U (getr regs 26)) ltac:(rewok W).
  zsd F_59440 D_59440 (sp - 128 + 24) (U (getr regs 27)) ltac:(rewok W).
  zstep F_59444 D_59444. zstep F_59448 D_59448. zstep F_5944c D_5944c. zstep F_59450 D_59450. zstep F_59454 D_59454. zstep F_59458 D_59458.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => set (Mf := X) end.
  assert (Ci' : cellA Mf 0x15d698 1 1) by (unfold Mf; unfold apart in *; recell Ci).
  assert (Cr' : cellA Mf 0x1dec22 1 0) by (unfold Mf; unfold apart in *; recell Cr).
  assert (R1' : cellA Mf 0x10460 8 0x218a392cd3d5dbf) by (unfold Mf; unfold apart in *; recell R1).
  assert (R2' : cellA Mf 0x104dc 1 3) by (unfold Mf; unfold apart in *; recell R2).
  stepn F_5945c D_5945c.
  zcall (art_asan_inited_fn _ _ _ _).
  zbft F_59460 D_59460.
  stepn F_59464 D_59464.
  zcall (art_rss_limit_fn _ _ _ _).
  zbft F_59468 D_59468.
  zbft F_5946c D_5946c.
  zstep F_59470 D_59470.
  zbtk F_59474 D_59474.
  zstep F_594b0 D_594b0. zstep F_594b4 D_594b4.
  zbtk F_594b8 D_594b8.
  zstep F_594c0 D_594c0. zstep F_594c4 D_594c4.
  zbft F_594c8 D_594c8.
  zstep F_594cc D_594cc. zld F_594d0 D_594d0 0x10460 R1'.
  zstep F_594d4 D_594d4. zstep F_594d8 D_594d8. zstep F_594dc D_594dc. zstep F_594e0 D_594e0. zstep F_594e4 D_594e4. zstep F_594e8 D_594e8.
  zstep F_594ec D_594ec.
  zlbu F_594f0 D_594f0 0x104dc R2'.
  zstep F_594f4 D_594f4. zstep F_594f8 D_594f8. zstep F_594fc D_594fc. zstep F_59500 D_59500.
  zbtk F_59504 D_59504.
  zstep F_59484 D_59484. zstep F_59488 D_59488. zstep F_5948c D_5948c.
  zbft F_59490 D_59490.
  zstep F_59494 D_59494. zstep F_59498 D_59498.
  zsd F_5949c D_5949c (sp - 128 + 8) 1 ltac:(unfold Mf; rewok W).
  zsd F_594a0 D_594a0 (sp - 128 + 16) 16 ltac:(unfold Mf; rewok W).
  unfold Mf, art_alloc_memA1. zret.
Qed.

Lemma art_alloc_ladder : forall regs (M rom : word -> option byte) (n : Z),
  getr regs 10 = Z_to_bv 64 49 -> getr regs 21 = Z_to_bv 64 n -> 1 <= n < 2 ^ 40 ->
  exists regs',
    msteps ASEGS (mkst regs (0x594f4 : word) M rom) (mkst regs' (0x595c8 : word) M rom)
    /\ getr regs' 19 = Z_to_bv 64 (AsanTab.rz_log n)
    /\ (forall r : reg, r <> 10%bv -> r <> 19%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom n H10 H21 Hn.
  unfold AsanTab.rz_log.
  destruct (Z.le_gt_cases n 48) as [C0|C0'].
  { eexists. split; [|split]; [ zbft F_594a4 D_594a4; zstep F_594a8 D_594a8; stepn F_594ac D_594ac; apply mst_refl | gres; zif; reflexivity | intros; kept_solve ]. }
  destruct (Z.le_gt_cases n 96) as [C1|C1'].
  { eexists. split; [|split]; [ zbtk F_594a4 D_594a4; zstep F_5950c D_5950c; zbft F_59510 D_59510; zstep F_59514 D_59514; stepn F_59518 D_59518; apply mst_refl
    | gres; zif; reflexivity | intros; kept_solve ]. }
  destruct (Z.le_gt_cases n 448) as [C2|C2'].
  { eexists. split; [|split]; [ zbtk F_594a4 D_594a4; zstep F_5950c D_5950c; zbtk F_59510 D_59510; zstep F_5951c D_5951c; zbft F_59520 D_59520; zstep F_59524 D_59524;
      stepn F_59528 D_59528; apply mst_refl | gres; zif; reflexivity | intros; kept_solve ]. }
  destruct (Z.le_gt_cases n 3968) as [C3|C3'].
  { eexists. split; [|split]; [ zbtk F_594a4 D_594a4; zstep F_5950c D_5950c; zbtk F_59510 D_59510; zstep F_5951c D_5951c; zbtk F_59520 D_59520;
      zstep F_5952c D_5952c; zstep F_59530 D_59530; zbft F_59534 D_59534; zstep F_59538 D_59538; stepn F_5953c D_5953c; apply mst_refl
    | gres; zif; reflexivity | intros; kept_solve ]. }
  destruct (Z.le_gt_cases n 16128) as [C4|C4'].
  { eexists. split; [|split]; [ zbtk F_594a4 D_594a4; zstep F_5950c D_5950c; zbtk F_59510 D_59510; zstep F_5951c D_5951c; zbtk F_59520 D_59520;
      zstep F_5952c D_5952c; zstep F_59530 D_59530; zbtk F_59534 D_59534; zstep F_59540 D_59540; zstep F_59544 D_59544; zbft F_59548 D_59548;
      zstep F_5954c D_5954c; stepn F_59550 D_59550; apply mst_refl
    | gres; zif; reflexivity | intros; kept_solve ]. }
  destruct (Z.le_gt_cases n 32256) as [C5|C5'].
  { eexists. split; [|split]; [ zbtk F_594a4 D_594a4; zstep F_5950c D_5950c; zbtk F_59510 D_59510; zstep F_5951c D_5951c; zbtk F_59520 D_59520;
      zstep F_5952c D_5952c; zstep F_59530 D_59530; zbtk F_59534 D_59534; zstep F_59540 D_59540; zstep F_59544 D_59544; zbtk F_59548 D_59548;
      zstep F_59554 D_59554; zstep F_59558 D_59558; zbft F_5955c D_5955c; zstep F_59560 D_59560; stepn F_59564 D_59564; apply mst_refl
    | gres; zif; reflexivity | intros; kept_solve ]. }

  eexists. split; [|split]; [ zbtk F_594a4 D_594a4; zstep F_5950c D_5950c; zbtk F_59510 D_59510; zstep F_5951c D_5951c; zbtk F_59520 D_59520;
      zstep F_5952c D_5952c; zstep F_59530 D_59530; zbtk F_59534 D_59534; zstep F_59540 D_59540; zstep F_59544 D_59544; zbtk F_59548 D_59548;
      zstep F_59554 D_59554; zstep F_59558 D_59558; zbtk F_5955c D_5955c; zstep F_59568 D_59568; zstep F_5956c D_5956c; zstep F_59570 D_59570;
      zstep F_59574 D_59574; apply mst_refl
    | gres | intros; kept_solve ].
  destruct (Z.le_gt_cases n 64512) as [C6|C6']; zif; vals_lit; reflexivity.
Qed.

Lemma art_alloc_a2_fn : forall regs (M rom : word -> option byte) (sp ia : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 26 = Z_to_bv 64 (ia + 2047) ->
  16 <= sp -> sp < 2 ^ 64 -> 4096 <= ia -> ia + 4096 <= 0x6b3000 ->
  wrA M (sp - 16) 16 -> 0x6b3000 + 16 <= sp ->
  art_rz_rodata M -> cellA M (ia + 3624) 2 16 -> cellA M (ia + 3626) 2 2048 ->
  msteps ASEGS (mkst regs (0x595c8 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x595f4 : bv 64)%bv) 2 (Z_to_bv 64 sp)) 9 (Z_to_bv 64 0)) 10 (Z_to_bv 64 7)) 11 (Z_to_bv 64 7)) 12 (Z_to_bv 64 11)) 13 (Z_to_bv 64 2048)) 14 (Z_to_bv 64 2048)) 20 (Z_to_bv 64 65536)) 24 (Z_to_bv 64 65535)) (0x595f4 : word) (Wn 8 (Wn 8 M (sp - 8) 0x595e0) (sp - 8) 0x595f4) rom).
Proof.
  intros regs M rom sp ia H2 H26 Hsp Hsp' Hia Hia' W IMG RO Cmin Cmax.
  zlh F_59578 D_59578 (ia + 3624) Cmin.
  stepfence F_5957c D_5957c.
  zstep F_59580 D_59580. zstep F_59584 D_59584. zstep F_59588 D_59588.
  stepn F_5958c D_5958c.
  zcall (art_rz2log_16_fn _ _ _ sp _).
  zstep F_59590 D_59590.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cmax' : cellA X (ia + 3626) 2 2048) by (unfold apart in *; recell Cmax) end.
  zlh F_59594 D_59594 (ia + 3626) Cmax'.
  stepfence F_59598 D_59598.
  zstep F_5959c D_5959c.
  stepn F_595a0 D_595a0.
  zcall (art_rz2log_2048_fn _ _ _ sp _).
  { destruct RO as (R1 & R2 & R3). unfold art_rz_rodata. repeat split; recell R1 || recell R2 || recell R3. }
  zret.
Qed.

Lemma art_alloc_clamp : forall regs (M rom : word -> option byte) (n r : Z),
  getr regs 9 = Z_to_bv 64 0 -> getr regs 10 = Z_to_bv 64 7 -> getr regs 19 = Z_to_bv 64 r -> getr regs 21 = Z_to_bv 64 n ->
  1 <= n < 2 ^ 40 -> r = AsanTab.rz_log n ->
  exists regs',
    msteps ASEGS (mkst regs (0x595f4 : word) M rom) (mkst regs' (0x59610 : word) M rom)
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
        [ zbft F_595a4 D_595a4; zstep F_595a8 D_595a8; zbft F_595ac D_595ac; zstep F_595b0 D_595b0; zstep F_595b4 D_595b4; zbft F_595b8 D_595b8; zstep F_595bc D_595bc; apply mst_refl
        | gres; f_equal; lia | gres; reflexivity | gres; rwH; f_equal; lia | intros; kept_solve ].
    + eexists. split; [|split; [|split; [|split]]];
        [ zbft F_595a4 D_595a4; zstep F_595a8 D_595a8; zbft F_595ac D_595ac; zstep F_595b0 D_595b0; zstep F_595b4 D_595b4; zbtk F_595b8 D_595b8; apply mst_refl
        | gres; rwH; f_equal; lia | gres; reflexivity | gres; rwH; f_equal; lia | intros; kept_solve ].
  - specialize (Rlo ltac:(lia)).
    eexists. split; [|split; [|split; [|split]]];
      [ zbtk F_595a4 D_595a4; zbtk F_59650 D_59650; zstep F_595b0 D_595b0; zstep F_595b4 D_595b4; zbtk F_595b8 D_595b8; apply mst_refl
      | gres; rwH; f_equal; lia | gres; reflexivity | gres; rwH; reflexivity | intros; kept_solve ].
  - specialize (R7 RS).
    eexists. split; [|split; [|split; [|split]]];
      [ zbtk F_595a4 D_595a4; zbft F_59650 D_59650; zstep F_59654 D_59654; zstep F_59658 D_59658; zstep F_5965c D_5965c; zbft F_59660 D_59660;
        stepn F_59664 D_59664; apply mst_refl
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

Lemma art_alloc_a3_fn : forall regs (M rom : word -> option byte) (sp ia n r rs rz tp key tsd ctx t : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> getr regs 8 = Z_to_bv 64 8 -> getr regs 10 = Z_to_bv 64 (Z.max n 8) ->
  getr regs 18 = Z_to_bv 64 8 -> getr regs 19 = Z_to_bv 64 r -> getr regs 20 = Z_to_bv 64 65536 -> getr regs 21 = Z_to_bv 64 n ->
  getr regs 22 = Z_to_bv 64 ia -> getr regs 26 = Z_to_bv 64 (ia + 2047) ->
  16 <= sp -> sp < 2 ^ 64 -> 4096 <= ia -> ia + 4096 <= 0x6b3000 -> 0x6b3000 + 16 <= sp ->
  1 <= n < 2 ^ 40 -> 0 <= r <= 7 -> rs = (Z.max n 8 + 7) / 8 * 8 -> rz = 16 * 2 ^ r -> rs + rz <= 65536 ->
  wrA M (sp - 16) 16 -> cellA M (ia + 3616) 8 (2 ^ 40) -> art_tsd M tp key tsd ctx t -> 1 <= t ->
  apart (sp - 16) 16 (tp - 88) 8 -> apart (sp - 16) 16 (tsd + 8 * key) 8 -> apart (sp - 16) 16 (ctx + 152) 8 ->
  msteps ASEGS (mkst regs (0x59610 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x596fc : bv 64)%bv) 2 (Z_to_bv 64 sp)) 8 (Z_to_bv 64 1)) 9 (Z_to_bv 64 n)) 10 (Z_to_bv 64 ia)) 11 (Z_to_bv 64 (t + 208))) 12 (Z_to_bv 64 (rs + rz))) 13 (Z_to_bv 64 8)) 19 (Z_to_bv 64 (rs + rz))) 20 (Z_to_bv 64 rz)) 24 (Z_to_bv 64 (2 ^ 64 - 8))) 26 (Z_to_bv 64 t)) (0x5dbb4 : word) (Wn 8 M (sp - 8) 0x596e0) rom).
Proof.
  intros regs M rom sp ia n r rs rz tp key tsd ctx t H2 H4 H8 H10 H18 H19 H20 H21 H22 H26 Hsp Hsp' Hia Hia' IMG Hn Hr Hrs Hrz Hprim W Cmax TSD Ht A1 A2 A3.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  assert (Hrs8 : rs mod 8 = 0) by (subst rs; apply Z_mod_mult).
  assert (Hrslo : 8 <= rs). { subst rs. pose proof (Z.mul_succ_div_gt (Z.max n 8 + 7) 8 ltac:(lia)). pose proof (Z.mul_div_le (Z.max n 8 + 7) 8 ltac:(lia)). lia. } assert (Hrz16 : 16 <= rz <= 2048) by (subst rz; split; [|change 2048 with (16 * 2 ^ 7); apply Z.mul_le_mono_nonneg_l; [lia|apply Z.pow_le_mono_r; lia]]; pose proof (Z.pow_pos_nonneg 2 r); nia).
  zstep F_595c0 D_595c0. zstep F_595c4 D_595c4. zstep F_595c8 D_595c8. zstep F_595cc D_595cc. zstep F_595d0 D_595d0.
  stepn F_595d4 D_595d4. rwH. rewrite art_zb_and by lia. rewrite art_land_m8 by lia.
  match goal with |- context [Z_to_bv 64 (?e / 8 * 8)] => replace (e / 8 * 8) with rs by (rewrite Hrs; f_equal; f_equal; lia) end.
  zstep F_595d8 D_595d8. zstep F_595dc D_595dc.
  stepn F_595e0 D_595e0. rwH. rewrite art_zb_andi by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8. rewrite Hrs8.
  zbft F_595e4 D_595e4.
  zstep F_595e8 D_595e8. zstep F_595ec D_595ec. zstep F_595f0 D_595f0.
  stepn F_595f4 D_595f4. rwH. rewrite art_zb_sllw_small by (subst rz; lia). rewrite <- Hrz.
  zstep F_595f8 D_595f8. zstep F_595fc D_595fc. zstep F_59600 D_59600. zstep F_59604 D_59604. zstep F_59608 D_59608. zstep F_5960c D_5960c.
  zstep F_59610 D_59610.
  stepn F_59614 D_59614. rwH. rewrite art_zb_and by lia. rewrite Z.land_0_l.
  zstep F_59618 D_59618. zstep F_5961c D_5961c.
  zbft F_59620 D_59620. zbft F_59624 D_59624.
  zld F_59628 D_59628 (ia + 3616) Cmax.
  zbtk F_5962c D_5962c.
  stepn F_5968c D_5968c.
  zcall (art_cur_thread_fn _ _ _ _ sp tp key tsd ctx t).
  zbft F_59694 D_59694 || (zstep F_59690 D_59690; zbft F_59694 D_59694).
  zstep F_59698 D_59698. zstep F_5969c D_5969c. zstep F_596a0 D_596a0. zstep F_596a4 D_596a4.
  stepn F_596a8 D_596a8.
  zret.
Qed.
End FPX.
