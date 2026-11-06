(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac Pm9ArtLeaf Pm9ArtRzLog.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm9_code_59000_5a000 .
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition art_alloc_rodata (M : word -> option byte) : Prop :=
  cellA M 0x10478 8 0x218a392cd3d5dbf /\ cellA M 0x104f4 1 3 /\ cellA M 0x10388 8 0xcc6e96b9cc6e96b9.

Definition art_alloc_memA1 (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
  (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 128 + 120) (U raw)) (sp - 128 + 112) (U (getr regs 8))) (sp - 128 + 104) (U (getr regs 9))) (sp - 128 + 96) (U (getr regs 18))) (sp - 128 + 88) (U (getr regs 19))) (sp - 128 + 80) (U (getr regs 20))) (sp - 128 + 72) (U (getr regs 21))) (sp - 128 + 64) (U (getr regs 22))) (sp - 128 + 56) (U (getr regs 23))) (sp - 128 + 48) (U (getr regs 24))) (sp - 128 + 40) (U (getr regs 25))) (sp - 128 + 32) (U (getr regs 26))) (sp - 128 + 24) (U (getr regs 27))) (sp - 128 + 8) 1) (sp - 128 + 16) 16).

Section FPX. Context {fx : PropExec.FPState}.

Lemma art_alloc_a1_fn : forall regs (M rom : word -> option byte) (raw : word) (sp ia n stk : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 ia -> getr regs 11 = Z_to_bv 64 n ->
  getr regs 12 = Z_to_bv 64 8 -> getr regs 13 = Z_to_bv 64 stk -> getr regs 14 = Z_to_bv 64 1 -> getr regs 15 = Z_to_bv 64 1 ->
  256 <= sp -> sp < 2 ^ 64 -> 4096 <= ia -> ia + 4096 < 2 ^ 64 -> 1 <= stk < 2 ^ 64 -> 1 <= n < 2 ^ 40 ->
  wrA M (sp - 256) 256 -> 0x6b4000 + 256 <= sp ->
  art_alloc_rodata M -> cellA M 0x15e9d8 1 1 -> cellA M 0x1dff62 1 0 ->
  msteps ASEGS (mkst regs (0x5981c : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x59878 : bv 64)%bv) 2 (Z_to_bv 64 (sp - 128))) 8 (Z_to_bv 64 8)) 9 (Z_to_bv 64 1)) 10 (Z_to_bv 64 49)) 11 (Z_to_bv 64 16)) 12 (Z_to_bv 64 0x104f0)) 13 (Z_to_bv 64 (2 ^ 64 - 8))) 18 (Z_to_bv 64 8)) 21 (Z_to_bv 64 n)) 22 (Z_to_bv 64 ia)) 23 (Z_to_bv 64 stk)) 25 (Z_to_bv 64 7)) 26 (Z_to_bv 64 (ia + 2047))) 27 (Z_to_bv 64 1)) (0x598b4 : word) (art_alloc_memA1 M sp raw regs) rom).
Proof.
  intros regs M rom raw sp ia n stk H1 H2 H10 H11 H12 H13 H14 H15 Hsp Hsp' Hia Hia' Hstk Hn W IMG (R1 & R2 & R3) Ci Cr.
  zstep F_597d4 D_597d4.
  zsd F_597d8 D_597d8 (sp - 128 + 120) (U raw) ltac:(rewok W).
  zsd F_597dc D_597dc (sp - 128 + 112) (U (getr regs 8)) ltac:(rewok W).
  zsd F_597e0 D_597e0 (sp - 128 + 104) (U (getr regs 9)) ltac:(rewok W).
  zsd F_597e4 D_597e4 (sp - 128 + 96) (U (getr regs 18)) ltac:(rewok W).
  zsd F_597e8 D_597e8 (sp - 128 + 88) (U (getr regs 19)) ltac:(rewok W).
  zsd F_597ec D_597ec (sp - 128 + 80) (U (getr regs 20)) ltac:(rewok W).
  zsd F_597f0 D_597f0 (sp - 128 + 72) (U (getr regs 21)) ltac:(rewok W).
  zsd F_597f4 D_597f4 (sp - 128 + 64) (U (getr regs 22)) ltac:(rewok W).
  zsd F_597f8 D_597f8 (sp - 128 + 56) (U (getr regs 23)) ltac:(rewok W).
  zsd F_597fc D_597fc (sp - 128 + 48) (U (getr regs 24)) ltac:(rewok W).
  zsd F_59800 D_59800 (sp - 128 + 40) (U (getr regs 25)) ltac:(rewok W).
  zsd F_59804 D_59804 (sp - 128 + 32) (U (getr regs 26)) ltac:(rewok W).
  zsd F_59808 D_59808 (sp - 128 + 24) (U (getr regs 27)) ltac:(rewok W).
  zstep F_5980c D_5980c. zstep F_59810 D_59810. zstep F_59814 D_59814. zstep F_59818 D_59818. zstep F_5981c D_5981c. zstep F_59820 D_59820.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => set (Mf := X) end.
  assert (Ci' : cellA Mf 0x15e9d8 1 1) by (unfold Mf; unfold apart in *; recell Ci).
  assert (Cr' : cellA Mf 0x1dff62 1 0) by (unfold Mf; unfold apart in *; recell Cr).
  assert (R1' : cellA Mf 0x10478 8 0x218a392cd3d5dbf) by (unfold Mf; unfold apart in *; recell R1).
  assert (R2' : cellA Mf 0x104f4 1 3) by (unfold Mf; unfold apart in *; recell R2).
  stepn F_59824 D_59824.
  zcall (art_asan_inited_fn _ _ _ _).
  zbft F_59828 D_59828.
  stepn F_5982c D_5982c.
  zcall (art_rss_limit_fn _ _ _ _).
  zbft F_59830 D_59830.
  zbft F_59834 D_59834.
  zstep F_59838 D_59838.
  zbtk F_5983c D_5983c.
  zstep F_59878 D_59878. zstep F_5987c D_5987c.
  zbtk F_59880 D_59880.
  zstep F_59888 D_59888. zstep F_5988c D_5988c.
  zbft F_59890 D_59890.
  zstep F_59894 D_59894. zld F_59898 D_59898 0x10478 R1'.
  zstep F_5989c D_5989c. zstep F_598a0 D_598a0. zstep F_598a4 D_598a4. zstep F_598a8 D_598a8. zstep F_598ac D_598ac. zstep F_598b0 D_598b0.
  zstep F_598b4 D_598b4.
  zlbu F_598b8 D_598b8 0x104f4 R2'.
  zstep F_598bc D_598bc. zstep F_598c0 D_598c0. zstep F_598c4 D_598c4. zstep F_598c8 D_598c8.
  zbtk F_598cc D_598cc.
  zstep F_5984c D_5984c. zstep F_59850 D_59850. zstep F_59854 D_59854.
  zbft F_59858 D_59858.
  zstep F_5985c D_5985c. zstep F_59860 D_59860.
  zsd F_59864 D_59864 (sp - 128 + 8) 1 ltac:(unfold Mf; rewok W).
  zsd F_59868 D_59868 (sp - 128 + 16) 16 ltac:(unfold Mf; rewok W).
  unfold Mf, art_alloc_memA1. zret.
Qed.

Lemma art_alloc_ladder : forall regs (M rom : word -> option byte) (n : Z),
  getr regs 10 = Z_to_bv 64 49 -> getr regs 21 = Z_to_bv 64 n -> 1 <= n < 2 ^ 40 ->
  exists regs',
    msteps ASEGS (mkst regs (0x598b4 : word) M rom) (mkst regs' (0x59988 : word) M rom)
    /\ getr regs' 19 = Z_to_bv 64 (AsanTab.rz_log n)
    /\ (forall r : reg, r <> 10%bv -> r <> 19%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom n H10 H21 Hn.
  unfold AsanTab.rz_log.
  destruct (Z.le_gt_cases n 48) as [C0|C0'].
  { eexists. split; [|split]; [ zbft F_5986c D_5986c; zstep F_59870 D_59870; stepn F_59874 D_59874; apply mst_refl | gres; zif; reflexivity | intros; kept_solve ]. }
  destruct (Z.le_gt_cases n 96) as [C1|C1'].
  { eexists. split; [|split]; [ zbtk F_5986c D_5986c; zstep F_598d4 D_598d4; zbft F_598d8 D_598d8; zstep F_598dc D_598dc; stepn F_598e0 D_598e0; apply mst_refl
    | gres; zif; reflexivity | intros; kept_solve ]. }
  destruct (Z.le_gt_cases n 448) as [C2|C2'].
  { eexists. split; [|split]; [ zbtk F_5986c D_5986c; zstep F_598d4 D_598d4; zbtk F_598d8 D_598d8; zstep F_598e4 D_598e4; zbft F_598e8 D_598e8; zstep F_598ec D_598ec;
      stepn F_598f0 D_598f0; apply mst_refl | gres; zif; reflexivity | intros; kept_solve ]. }
  destruct (Z.le_gt_cases n 3968) as [C3|C3'].
  { eexists. split; [|split]; [ zbtk F_5986c D_5986c; zstep F_598d4 D_598d4; zbtk F_598d8 D_598d8; zstep F_598e4 D_598e4; zbtk F_598e8 D_598e8;
      zstep F_598f4 D_598f4; zstep F_598f8 D_598f8; zbft F_598fc D_598fc; zstep F_59900 D_59900; stepn F_59904 D_59904; apply mst_refl
    | gres; zif; reflexivity | intros; kept_solve ]. }
  destruct (Z.le_gt_cases n 16128) as [C4|C4'].
  { eexists. split; [|split]; [ zbtk F_5986c D_5986c; zstep F_598d4 D_598d4; zbtk F_598d8 D_598d8; zstep F_598e4 D_598e4; zbtk F_598e8 D_598e8;
      zstep F_598f4 D_598f4; zstep F_598f8 D_598f8; zbtk F_598fc D_598fc; zstep F_59908 D_59908; zstep F_5990c D_5990c; zbft F_59910 D_59910;
      zstep F_59914 D_59914; stepn F_59918 D_59918; apply mst_refl
    | gres; zif; reflexivity | intros; kept_solve ]. }
  destruct (Z.le_gt_cases n 32256) as [C5|C5'].
  { eexists. split; [|split]; [ zbtk F_5986c D_5986c; zstep F_598d4 D_598d4; zbtk F_598d8 D_598d8; zstep F_598e4 D_598e4; zbtk F_598e8 D_598e8;
      zstep F_598f4 D_598f4; zstep F_598f8 D_598f8; zbtk F_598fc D_598fc; zstep F_59908 D_59908; zstep F_5990c D_5990c; zbtk F_59910 D_59910;
      zstep F_5991c D_5991c; zstep F_59920 D_59920; zbft F_59924 D_59924; zstep F_59928 D_59928; stepn F_5992c D_5992c; apply mst_refl
    | gres; zif; reflexivity | intros; kept_solve ]. }

  eexists. split; [|split]; [ zbtk F_5986c D_5986c; zstep F_598d4 D_598d4; zbtk F_598d8 D_598d8; zstep F_598e4 D_598e4; zbtk F_598e8 D_598e8;
      zstep F_598f4 D_598f4; zstep F_598f8 D_598f8; zbtk F_598fc D_598fc; zstep F_59908 D_59908; zstep F_5990c D_5990c; zbtk F_59910 D_59910;
      zstep F_5991c D_5991c; zstep F_59920 D_59920; zbtk F_59924 D_59924; zstep F_59930 D_59930; zstep F_59934 D_59934; zstep F_59938 D_59938;
      zstep F_5993c D_5993c; apply mst_refl
    | gres | intros; kept_solve ].
  destruct (Z.le_gt_cases n 64512) as [C6|C6']; zif; vals_lit; reflexivity.
Qed.

Lemma art_alloc_a2_fn : forall regs (M rom : word -> option byte) (sp ia : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 26 = Z_to_bv 64 (ia + 2047) ->
  16 <= sp -> sp < 2 ^ 64 -> 4096 <= ia -> ia + 4096 <= 0x6b4000 ->
  wrA M (sp - 16) 16 -> 0x6b4000 + 16 <= sp ->
  art_rz_rodata M -> cellA M (ia + 3624) 2 16 -> cellA M (ia + 3626) 2 2048 ->
  msteps ASEGS (mkst regs (0x59988 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x599b4 : bv 64)%bv) 2 (Z_to_bv 64 sp)) 9 (Z_to_bv 64 0)) 10 (Z_to_bv 64 7)) 11 (Z_to_bv 64 7)) 12 (Z_to_bv 64 11)) 13 (Z_to_bv 64 2048)) 14 (Z_to_bv 64 2048)) 20 (Z_to_bv 64 65536)) 24 (Z_to_bv 64 65535)) (0x599b4 : word) (Wn 8 (Wn 8 M (sp - 8) 0x599a0) (sp - 8) 0x599b4) rom).
Proof.
  intros regs M rom sp ia H2 H26 Hsp Hsp' Hia Hia' W IMG RO Cmin Cmax.
  zlh F_59940 D_59940 (ia + 3624) Cmin.
  stepfence F_59944 D_59944.
  zstep F_59948 D_59948. zstep F_5994c D_5994c. zstep F_59950 D_59950.
  stepn F_59954 D_59954.
  zcall (art_rz2log_16_fn _ _ _ sp _).
  zstep F_59958 D_59958.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cmax' : cellA X (ia + 3626) 2 2048) by (unfold apart in *; recell Cmax) end.
  zlh F_5995c D_5995c (ia + 3626) Cmax'.
  stepfence F_59960 D_59960.
  zstep F_59964 D_59964.
  stepn F_59968 D_59968.
  zcall (art_rz2log_2048_fn _ _ _ sp _).
  { destruct RO as (R1 & R2 & R3). unfold art_rz_rodata. repeat split; recell R1 || recell R2 || recell R3. }
  zret.
Qed.

Lemma art_alloc_clamp : forall regs (M rom : word -> option byte) (n r : Z),
  getr regs 9 = Z_to_bv 64 0 -> getr regs 10 = Z_to_bv 64 7 -> getr regs 19 = Z_to_bv 64 r -> getr regs 21 = Z_to_bv 64 n ->
  1 <= n < 2 ^ 40 -> r = AsanTab.rz_log n ->
  exists regs',
    msteps ASEGS (mkst regs (0x599b4 : word) M rom) (mkst regs' (0x599d0 : word) M rom)
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
        [ zbft F_5996c D_5996c; zstep F_59970 D_59970; zbft F_59974 D_59974; zstep F_59978 D_59978; zstep F_5997c D_5997c; zbft F_59980 D_59980; zstep F_59984 D_59984; apply mst_refl
        | gres; f_equal; lia | gres; reflexivity | gres; rwH; f_equal; lia | intros; kept_solve ].
    + eexists. split; [|split; [|split; [|split]]];
        [ zbft F_5996c D_5996c; zstep F_59970 D_59970; zbft F_59974 D_59974; zstep F_59978 D_59978; zstep F_5997c D_5997c; zbtk F_59980 D_59980; apply mst_refl
        | gres; rwH; f_equal; lia | gres; reflexivity | gres; rwH; f_equal; lia | intros; kept_solve ].
  - specialize (Rlo ltac:(lia)).
    eexists. split; [|split; [|split; [|split]]];
      [ zbtk F_5996c D_5996c; zbtk F_59a18 D_59a18; zstep F_59978 D_59978; zstep F_5997c D_5997c; zbtk F_59980 D_59980; apply mst_refl
      | gres; rwH; f_equal; lia | gres; reflexivity | gres; rwH; reflexivity | intros; kept_solve ].
  - specialize (R7 RS).
    eexists. split; [|split; [|split; [|split]]];
      [ zbtk F_5996c D_5996c; zbft F_59a18 D_59a18; zstep F_59a1c D_59a1c; zstep F_59a20 D_59a20; zstep F_59a24 D_59a24; zbft F_59a28 D_59a28;
        stepn F_59a2c D_59a2c; apply mst_refl
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
  16 <= sp -> sp < 2 ^ 64 -> 4096 <= ia -> ia + 4096 <= 0x6b4000 -> 0x6b4000 + 16 <= sp ->
  1 <= n < 2 ^ 40 -> 0 <= r <= 7 -> rs = (Z.max n 8 + 7) / 8 * 8 -> rz = 16 * 2 ^ r -> rs + rz <= 65536 ->
  wrA M (sp - 16) 16 -> cellA M (ia + 3616) 8 (2 ^ 40) -> art_tsd M tp key tsd ctx t -> 1 <= t ->
  apart (sp - 16) 16 (tp - 88) 8 -> apart (sp - 16) 16 (tsd + 8 * key) 8 -> apart (sp - 16) 16 (ctx + 152) 8 ->
  msteps ASEGS (mkst regs (0x599d0 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x59abc : bv 64)%bv) 2 (Z_to_bv 64 sp)) 8 (Z_to_bv 64 1)) 9 (Z_to_bv 64 n)) 10 (Z_to_bv 64 ia)) 11 (Z_to_bv 64 (t + 208))) 12 (Z_to_bv 64 (rs + rz))) 13 (Z_to_bv 64 8)) 19 (Z_to_bv 64 (rs + rz))) 20 (Z_to_bv 64 rz)) 24 (Z_to_bv 64 (2 ^ 64 - 8))) 26 (Z_to_bv 64 t)) (0x5df74 : word) (Wn 8 M (sp - 8) 0x59aa0) rom).
Proof.
  intros regs M rom sp ia n r rs rz tp key tsd ctx t H2 H4 H8 H10 H18 H19 H20 H21 H22 H26 Hsp Hsp' Hia Hia' IMG Hn Hr Hrs Hrz Hprim W Cmax TSD Ht A1 A2 A3.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  assert (Hrs8 : rs mod 8 = 0) by (subst rs; apply Z_mod_mult).
  assert (Hrslo : 8 <= rs). { subst rs. pose proof (Z.mul_succ_div_gt (Z.max n 8 + 7) 8 ltac:(lia)). pose proof (Z.mul_div_le (Z.max n 8 + 7) 8 ltac:(lia)). lia. } assert (Hrz16 : 16 <= rz <= 2048) by (subst rz; split; [|change 2048 with (16 * 2 ^ 7); apply Z.mul_le_mono_nonneg_l; [lia|apply Z.pow_le_mono_r; lia]]; pose proof (Z.pow_pos_nonneg 2 r); nia).
  zstep F_59988 D_59988. zstep F_5998c D_5998c. zstep F_59990 D_59990. zstep F_59994 D_59994. zstep F_59998 D_59998.
  stepn F_5999c D_5999c. rwH. rewrite art_zb_and by lia. rewrite art_land_m8 by lia.
  match goal with |- context [Z_to_bv 64 (?e / 8 * 8)] => replace (e / 8 * 8) with rs by (rewrite Hrs; f_equal; f_equal; lia) end.
  zstep F_599a0 D_599a0. zstep F_599a4 D_599a4.
  stepn F_599a8 D_599a8. rwH. rewrite art_zb_andi by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8. rewrite Hrs8.
  zbft F_599ac D_599ac.
  zstep F_599b0 D_599b0. zstep F_599b4 D_599b4. zstep F_599b8 D_599b8.
  stepn F_599bc D_599bc. rwH. rewrite art_zb_sllw_small by (subst rz; lia). rewrite <- Hrz.
  zstep F_599c0 D_599c0. zstep F_599c4 D_599c4. zstep F_599c8 D_599c8. zstep F_599cc D_599cc. zstep F_599d0 D_599d0. zstep F_599d4 D_599d4.
  zstep F_599d8 D_599d8.
  stepn F_599dc D_599dc. rwH. rewrite art_zb_and by lia. rewrite Z.land_0_l.
  zstep F_599e0 D_599e0. zstep F_599e4 D_599e4.
  zbft F_599e8 D_599e8. zbft F_599ec D_599ec.
  zld F_599f0 D_599f0 (ia + 3616) Cmax.
  zbtk F_599f4 D_599f4.
  stepn F_59a54 D_59a54.
  zcall (art_cur_thread_fn _ _ _ _ sp tp key tsd ctx t).
  zbft F_59a5c D_59a5c || (zstep F_59a58 D_59a58; zbft F_59a5c D_59a5c).
  zstep F_59a60 D_59a60. zstep F_59a64 D_59a64. zstep F_59a68 D_59a68. zstep F_59a6c D_59a6c.
  stepn F_59a70 D_59a70.
  zret.
Qed.
End FPX.
