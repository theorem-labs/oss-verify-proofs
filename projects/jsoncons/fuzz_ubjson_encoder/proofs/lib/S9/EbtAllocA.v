(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import As0Tables.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import ArtMem ArtRegs ArtAtomics ArtTac EbtLeaf EbtRzLog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_r3cf10_3de98.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition art_alloc_rodata (M : word -> option byte) : Prop :=
  cellA M 0x10450 8 0x218a392cd3d5dbf /\ cellA M 0x104cc 1 3 /\ cellA M 0x10378 8 0xcc6e96b9cc6e96b9.

Definition art_alloc_memA1 (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
  (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 128 + 120) (U raw)) (sp - 128 + 112) (U (getr regs 8))) (sp - 128 + 104) (U (getr regs 9))) (sp - 128 + 96) (U (getr regs 18))) (sp - 128 + 88) (U (getr regs 19))) (sp - 128 + 80) (U (getr regs 20))) (sp - 128 + 72) (U (getr regs 21))) (sp - 128 + 64) (U (getr regs 22))) (sp - 128 + 56) (U (getr regs 23))) (sp - 128 + 48) (U (getr regs 24))) (sp - 128 + 40) (U (getr regs 25))) (sp - 128 + 32) (U (getr regs 26))) (sp - 128 + 24) (U (getr regs 27))) (sp - 128 + 8) 1) (sp - 128 + 16) 16).

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_alloc_a1_fn : forall regs (M rom : word -> option byte) (raw : word) (sp ia n stk : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 ia -> getr regs 11 = Z_to_bv 64 n ->
  getr regs 12 = Z_to_bv 64 8 -> getr regs 13 = Z_to_bv 64 stk -> getr regs 14 = Z_to_bv 64 1 -> getr regs 15 = Z_to_bv 64 1 ->
  256 <= sp -> sp < 2 ^ 64 -> 4096 <= ia -> ia + 4096 < 2 ^ 64 -> 1 <= stk < 2 ^ 64 -> 1 <= n < 2 ^ 40 ->
  wrA M (sp - 256) 256 -> 0x69c000 + 256 <= sp ->
  art_alloc_rodata M -> cellA M 0x146dd8 1 1 -> cellA M 0x1c8362 1 0 ->
  msteps ASEGS (mkst regs (0x535f4 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x53650 : bv 64)%bv) 2 (Z_to_bv 64 (sp - 128))) 8 (Z_to_bv 64 8)) 9 (Z_to_bv 64 1)) 10 (Z_to_bv 64 49)) 11 (Z_to_bv 64 16)) 12 (Z_to_bv 64 0x104c8)) 13 (Z_to_bv 64 (2 ^ 64 - 8))) 18 (Z_to_bv 64 8)) 21 (Z_to_bv 64 n)) 22 (Z_to_bv 64 ia)) 23 (Z_to_bv 64 stk)) 25 (Z_to_bv 64 7)) 26 (Z_to_bv 64 (ia + 2047))) 27 (Z_to_bv 64 1)) (0x5368c : word) (art_alloc_memA1 M sp raw regs) rom).
Proof.
  intros regs M rom raw sp ia n stk H1 H2 H10 H11 H12 H13 H14 H15 Hsp Hsp' Hia Hia' Hstk Hn W IMG (R1 & R2 & R3) Ci Cr.
  zstep F_535a4 D_535a4.
  zsd F_535a8 D_535a8 (sp - 128 + 120) (U raw) ltac:(rewok W).
  zsd F_535ac D_535ac (sp - 128 + 112) (U (getr regs 8)) ltac:(rewok W).
  zsd F_535b0 D_535b0 (sp - 128 + 104) (U (getr regs 9)) ltac:(rewok W).
  zsd F_535b4 D_535b4 (sp - 128 + 96) (U (getr regs 18)) ltac:(rewok W).
  zsd F_535b8 D_535b8 (sp - 128 + 88) (U (getr regs 19)) ltac:(rewok W).
  zsd F_535bc D_535bc (sp - 128 + 80) (U (getr regs 20)) ltac:(rewok W).
  zsd F_535c0 D_535c0 (sp - 128 + 72) (U (getr regs 21)) ltac:(rewok W).
  zsd F_535c4 D_535c4 (sp - 128 + 64) (U (getr regs 22)) ltac:(rewok W).
  zsd F_535c8 D_535c8 (sp - 128 + 56) (U (getr regs 23)) ltac:(rewok W).
  zsd F_535cc D_535cc (sp - 128 + 48) (U (getr regs 24)) ltac:(rewok W).
  zsd F_535d0 D_535d0 (sp - 128 + 40) (U (getr regs 25)) ltac:(rewok W).
  zsd F_535d4 D_535d4 (sp - 128 + 32) (U (getr regs 26)) ltac:(rewok W).
  zsd F_535d8 D_535d8 (sp - 128 + 24) (U (getr regs 27)) ltac:(rewok W).
  zstep F_535dc D_535dc. zstep F_535e0 D_535e0. zstep F_535e4 D_535e4. zstep F_535e8 D_535e8. zstep F_535ec D_535ec. zstep F_535f0 D_535f0.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => set (Mf := X) end.
  assert (Ci' : cellA Mf 0x146dd8 1 1) by (unfold Mf; unfold apart in *; recell Ci).
  assert (Cr' : cellA Mf 0x1c8362 1 0) by (unfold Mf; unfold apart in *; recell Cr).
  assert (R1' : cellA Mf 0x10450 8 0x218a392cd3d5dbf) by (unfold Mf; unfold apart in *; recell R1).
  assert (R2' : cellA Mf 0x104cc 1 3) by (unfold Mf; unfold apart in *; recell R2).
  stepn F_535f4 D_535f4.
  zcall (art_asan_inited_fn _ _ _ _).
  zbft F_535f8 D_535f8.
  stepn F_535fc D_535fc.
  zcall (art_rss_limit_fn _ _ _ _).
  zbft F_53600 D_53600.
  zbft F_53604 D_53604.
  zstep F_53608 D_53608.
  zbtk F_5360c D_5360c.
  zstep F_53648 D_53648. zstep F_5364c D_5364c.
  zbtk F_53650 D_53650.
  zstep F_53658 D_53658. zstep F_5365c D_5365c.
  zbft F_53660 D_53660.
  zstep F_53664 D_53664. zld F_53668 D_53668 0x10450 R1'.
  zstep F_5366c D_5366c. zstep F_53670 D_53670. zstep F_53674 D_53674. zstep F_53678 D_53678. zstep F_5367c D_5367c. zstep F_53680 D_53680.
  zstep F_53684 D_53684.
  zlbu F_53688 D_53688 0x104cc R2'.
  zstep F_5368c D_5368c. zstep F_53690 D_53690. zstep F_53694 D_53694. zstep F_53698 D_53698.
  zbtk F_5369c D_5369c.
  zstep F_5361c D_5361c. zstep F_53620 D_53620. zstep F_53624 D_53624.
  zbft F_53628 D_53628.
  zstep F_5362c D_5362c. zstep F_53630 D_53630.
  zsd F_53634 D_53634 (sp - 128 + 8) 1 ltac:(unfold Mf; rewok W).
  zsd F_53638 D_53638 (sp - 128 + 16) 16 ltac:(unfold Mf; rewok W).
  unfold Mf, art_alloc_memA1. zret.
Qed.

#[using="Type"] Lemma art_alloc_ladder : forall regs (M rom : word -> option byte) (n : Z),
  getr regs 10 = Z_to_bv 64 49 -> getr regs 21 = Z_to_bv 64 n -> 1 <= n < 2 ^ 40 ->
  exists regs',
    msteps ASEGS (mkst regs (0x5368c : word) M rom) (mkst regs' (0x53760 : word) M rom)
    /\ getr regs' 19 = Z_to_bv 64 (AsanTab.rz_log n)
    /\ (forall r : reg, r <> 10%bv -> r <> 19%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom n H10 H21 Hn.
  unfold AsanTab.rz_log.
  destruct (Z.le_gt_cases n 48) as [C0|C0'].
  { eexists. split; [|split]; [ zbft F_5363c D_5363c; zstep F_53640 D_53640; stepn F_53644 D_53644; apply mst_refl | gres; zif; reflexivity | intros; kept_solve ]. }
  destruct (Z.le_gt_cases n 96) as [C1|C1'].
  { eexists. split; [|split]; [ zbtk F_5363c D_5363c; zstep F_536a4 D_536a4; zbft F_536a8 D_536a8; zstep F_536ac D_536ac; stepn F_536b0 D_536b0; apply mst_refl
    | gres; zif; reflexivity | intros; kept_solve ]. }
  destruct (Z.le_gt_cases n 448) as [C2|C2'].
  { eexists. split; [|split]; [ zbtk F_5363c D_5363c; zstep F_536a4 D_536a4; zbtk F_536a8 D_536a8; zstep F_536b4 D_536b4; zbft F_536b8 D_536b8; zstep F_536bc D_536bc;
      stepn F_536c0 D_536c0; apply mst_refl | gres; zif; reflexivity | intros; kept_solve ]. }
  destruct (Z.le_gt_cases n 3968) as [C3|C3'].
  { eexists. split; [|split]; [ zbtk F_5363c D_5363c; zstep F_536a4 D_536a4; zbtk F_536a8 D_536a8; zstep F_536b4 D_536b4; zbtk F_536b8 D_536b8;
      zstep F_536c4 D_536c4; zstep F_536c8 D_536c8; zbft F_536cc D_536cc; zstep F_536d0 D_536d0; stepn F_536d4 D_536d4; apply mst_refl
    | gres; zif; reflexivity | intros; kept_solve ]. }
  destruct (Z.le_gt_cases n 16128) as [C4|C4'].
  { eexists. split; [|split]; [ zbtk F_5363c D_5363c; zstep F_536a4 D_536a4; zbtk F_536a8 D_536a8; zstep F_536b4 D_536b4; zbtk F_536b8 D_536b8;
      zstep F_536c4 D_536c4; zstep F_536c8 D_536c8; zbtk F_536cc D_536cc; zstep F_536d8 D_536d8; zstep F_536dc D_536dc; zbft F_536e0 D_536e0;
      zstep F_536e4 D_536e4; stepn F_536e8 D_536e8; apply mst_refl
    | gres; zif; reflexivity | intros; kept_solve ]. }
  destruct (Z.le_gt_cases n 32256) as [C5|C5'].
  { eexists. split; [|split]; [ zbtk F_5363c D_5363c; zstep F_536a4 D_536a4; zbtk F_536a8 D_536a8; zstep F_536b4 D_536b4; zbtk F_536b8 D_536b8;
      zstep F_536c4 D_536c4; zstep F_536c8 D_536c8; zbtk F_536cc D_536cc; zstep F_536d8 D_536d8; zstep F_536dc D_536dc; zbtk F_536e0 D_536e0;
      zstep F_536ec D_536ec; zstep F_536f0 D_536f0; zbft F_536f4 D_536f4; zstep F_536f8 D_536f8; stepn F_536fc D_536fc; apply mst_refl
    | gres; zif; reflexivity | intros; kept_solve ]. }

  eexists. split; [|split]; [ zbtk F_5363c D_5363c; zstep F_536a4 D_536a4; zbtk F_536a8 D_536a8; zstep F_536b4 D_536b4; zbtk F_536b8 D_536b8;
      zstep F_536c4 D_536c4; zstep F_536c8 D_536c8; zbtk F_536cc D_536cc; zstep F_536d8 D_536d8; zstep F_536dc D_536dc; zbtk F_536e0 D_536e0;
      zstep F_536ec D_536ec; zstep F_536f0 D_536f0; zbtk F_536f4 D_536f4; zstep F_53700 D_53700; zstep F_53704 D_53704; zstep F_53708 D_53708;
      zstep F_5370c D_5370c; apply mst_refl
    | gres | intros; kept_solve ].
  destruct (Z.le_gt_cases n 64512) as [C6|C6']; zif; vals_lit; reflexivity.
Qed.

#[using="Type"] Lemma art_alloc_a2_fn : forall regs (M rom : word -> option byte) (sp ia : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 26 = Z_to_bv 64 (ia + 2047) ->
  16 <= sp -> sp < 2 ^ 64 -> 4096 <= ia -> ia + 4096 <= 0x69c000 ->
  wrA M (sp - 16) 16 -> 0x69c000 + 16 <= sp ->
  art_rz_rodata M -> cellA M (ia + 3624) 2 16 -> cellA M (ia + 3626) 2 2048 ->
  msteps ASEGS (mkst regs (0x53760 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x5378c : bv 64)%bv) 2 (Z_to_bv 64 sp)) 9 (Z_to_bv 64 0)) 10 (Z_to_bv 64 7)) 11 (Z_to_bv 64 7)) 12 (Z_to_bv 64 11)) 13 (Z_to_bv 64 2048)) 14 (Z_to_bv 64 2048)) 20 (Z_to_bv 64 65536)) 24 (Z_to_bv 64 65535)) (0x5378c : word) (Wn 8 (Wn 8 M (sp - 8) 0x53778) (sp - 8) 0x5378c) rom).
Proof.
  intros regs M rom sp ia H2 H26 Hsp Hsp' Hia Hia' W IMG RO Cmin Cmax.
  zlh F_53710 D_53710 (ia + 3624) Cmin.
  stepfence F_53714 D_53714.
  zstep F_53718 D_53718. zstep F_5371c D_5371c. zstep F_53720 D_53720.
  stepn F_53724 D_53724.
  zcall (art_rz2log_16_fn _ _ _ sp _).
  zstep F_53728 D_53728.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cmax' : cellA X (ia + 3626) 2 2048) by (unfold apart in *; recell Cmax) end.
  zlh F_5372c D_5372c (ia + 3626) Cmax'.
  stepfence F_53730 D_53730.
  zstep F_53734 D_53734.
  stepn F_53738 D_53738.
  zcall (art_rz2log_2048_fn _ _ _ sp _).
  { destruct RO as (R1 & R2 & R3). unfold art_rz_rodata. repeat split; recell R1 || recell R2 || recell R3. }
  zret.
Qed.

#[using="Type"] Lemma art_alloc_clamp : forall regs (M rom : word -> option byte) (n r : Z),
  getr regs 9 = Z_to_bv 64 0 -> getr regs 10 = Z_to_bv 64 7 -> getr regs 19 = Z_to_bv 64 r -> getr regs 21 = Z_to_bv 64 n ->
  1 <= n < 2 ^ 40 -> r = AsanTab.rz_log n ->
  exists regs',
    msteps ASEGS (mkst regs (0x5378c : word) M rom) (mkst regs' (0x537a8 : word) M rom)
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
        [ zbft F_5373c D_5373c; zstep F_53740 D_53740; zbft F_53744 D_53744; zstep F_53748 D_53748; zstep F_5374c D_5374c; zbft F_53750 D_53750; zstep F_53754 D_53754; apply mst_refl
        | gres; f_equal; lia | gres; reflexivity | gres; rwH; f_equal; lia | intros; kept_solve ].
    + eexists. split; [|split; [|split; [|split]]];
        [ zbft F_5373c D_5373c; zstep F_53740 D_53740; zbft F_53744 D_53744; zstep F_53748 D_53748; zstep F_5374c D_5374c; zbtk F_53750 D_53750; apply mst_refl
        | gres; rwH; f_equal; lia | gres; reflexivity | gres; rwH; f_equal; lia | intros; kept_solve ].
  - specialize (Rlo ltac:(lia)).
    eexists. split; [|split; [|split; [|split]]];
      [ zbtk F_5373c D_5373c; zbtk F_537e8 D_537e8; zstep F_53748 D_53748; zstep F_5374c D_5374c; zbtk F_53750 D_53750; apply mst_refl
      | gres; rwH; f_equal; lia | gres; reflexivity | gres; rwH; reflexivity | intros; kept_solve ].
  - specialize (R7 RS).
    eexists. split; [|split; [|split; [|split]]];
      [ zbtk F_5373c D_5373c; zbft F_537e8 D_537e8; zstep F_537ec D_537ec; zstep F_537f0 D_537f0; zstep F_537f4 D_537f4; zbft F_537f8 D_537f8;
        stepn F_537fc D_537fc; apply mst_refl
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
  16 <= sp -> sp < 2 ^ 64 -> 4096 <= ia -> ia + 4096 <= 0x69c000 -> 0x69c000 + 16 <= sp ->
  1 <= n < 2 ^ 40 -> 0 <= r <= 7 -> rs = (Z.max n 8 + 7) / 8 * 8 -> rz = 16 * 2 ^ r -> rs + rz <= 65536 ->
  wrA M (sp - 16) 16 -> cellA M (ia + 3616) 8 (2 ^ 40) -> art_tsd M tp key tsd ctx t -> 1 <= t ->
  apart (sp - 16) 16 (tp - 88) 8 -> apart (sp - 16) 16 (tsd + 8 * key) 8 -> apart (sp - 16) 16 (ctx + 152) 8 ->
  msteps ASEGS (mkst regs (0x537a8 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x53894 : bv 64)%bv) 2 (Z_to_bv 64 sp)) 8 (Z_to_bv 64 1)) 9 (Z_to_bv 64 n)) 10 (Z_to_bv 64 ia)) 11 (Z_to_bv 64 (t + 208))) 12 (Z_to_bv 64 (rs + rz))) 13 (Z_to_bv 64 8)) 19 (Z_to_bv 64 (rs + rz))) 20 (Z_to_bv 64 rz)) 24 (Z_to_bv 64 (2 ^ 64 - 8))) 26 (Z_to_bv 64 t)) (0x57d4c : word) (Wn 8 M (sp - 8) 0x53878) rom).
Proof.
  intros regs M rom sp ia n r rs rz tp key tsd ctx t H2 H4 H8 H10 H18 H19 H20 H21 H22 H26 Hsp Hsp' Hia Hia' IMG Hn Hr Hrs Hrz Hprim W Cmax TSD Ht A1 A2 A3.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  assert (Hrs8 : rs mod 8 = 0) by (subst rs; apply Z_mod_mult).
  assert (Hrslo : 8 <= rs). { subst rs. pose proof (Z.mul_succ_div_gt (Z.max n 8 + 7) 8 ltac:(lia)). pose proof (Z.mul_div_le (Z.max n 8 + 7) 8 ltac:(lia)). lia. } assert (Hrz16 : 16 <= rz <= 2048) by (subst rz; split; [|change 2048 with (16 * 2 ^ 7); apply Z.mul_le_mono_nonneg_l; [lia|apply Z.pow_le_mono_r; lia]]; pose proof (Z.pow_pos_nonneg 2 r); nia).
  zstep F_53758 D_53758. zstep F_5375c D_5375c. zstep F_53760 D_53760. zstep F_53764 D_53764. zstep F_53768 D_53768.
  stepn F_5376c D_5376c. rwH. rewrite art_zb_and by lia. rewrite art_land_m8 by lia.
  match goal with |- context [Z_to_bv 64 (?e / 8 * 8)] => replace (e / 8 * 8) with rs by (rewrite Hrs; f_equal; f_equal; lia) end.
  zstep F_53770 D_53770. zstep F_53774 D_53774.
  stepn F_53778 D_53778. rwH. rewrite art_zb_andi by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8. rewrite Hrs8.
  zbft F_5377c D_5377c.
  zstep F_53780 D_53780. zstep F_53784 D_53784. zstep F_53788 D_53788.
  stepn F_5378c D_5378c. rwH. rewrite art_zb_sllw_small by (subst rz; lia). rewrite <- Hrz.
  zstep F_53790 D_53790. zstep F_53794 D_53794. zstep F_53798 D_53798. zstep F_5379c D_5379c. zstep F_537a0 D_537a0. zstep F_537a4 D_537a4.
  zstep F_537a8 D_537a8.
  stepn F_537ac D_537ac. rwH. rewrite art_zb_and by lia. rewrite Z.land_0_l.
  zstep F_537b0 D_537b0. zstep F_537b4 D_537b4.
  zbft F_537b8 D_537b8. zbft F_537bc D_537bc.
  zld F_537c0 D_537c0 (ia + 3616) Cmax.
  zbtk F_537c4 D_537c4.
  stepn F_53824 D_53824.
  zcall (art_cur_thread_fn _ _ _ _ sp tp key tsd ctx t).
  zbft F_5382c D_5382c || (zstep F_53828 D_53828; zbft F_5382c D_5382c).
  zstep F_53830 D_53830. zstep F_53834 D_53834. zstep F_53838 D_53838. zstep F_5383c D_5383c.
  stepn F_53840 D_53840.
  zret.
Qed.
End FPX.
