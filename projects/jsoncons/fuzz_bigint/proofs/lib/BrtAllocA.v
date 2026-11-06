(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac BrtLeaf BrtRzLog.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import Bo0_code_3d2b4_3e23c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
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
  wrA M (sp - 256) 256 -> 0x634000 + 256 <= sp ->
  art_alloc_rodata M -> cellA M 0xdf418 1 1 -> cellA M 0x1609a2 1 0 ->
  msteps ASEGS (mkst regs (0x3d5f0 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x3d64c : bv 64)%bv) 2 (Z_to_bv 64 (sp - 128))) 8 (Z_to_bv 64 8)) 9 (Z_to_bv 64 1)) 10 (Z_to_bv 64 49)) 11 (Z_to_bv 64 16)) 12 (Z_to_bv 64 0x10458)) 13 (Z_to_bv 64 (2 ^ 64 - 8))) 18 (Z_to_bv 64 8)) 21 (Z_to_bv 64 n)) 22 (Z_to_bv 64 ia)) 23 (Z_to_bv 64 stk)) 25 (Z_to_bv 64 7)) 26 (Z_to_bv 64 (ia + 2047))) 27 (Z_to_bv 64 1)) (0x3d688 : word) (art_alloc_memA1 M sp raw regs) rom).
Proof.
  intros regs M rom raw sp ia n stk H1 H2 H10 H11 H12 H13 H14 H15 Hsp Hsp' Hia Hia' Hstk Hn W IMG (R1 & R2 & R3) Ci Cr.
  zstep F_3d5f0 D_3d5f0.
  zsd F_3d5f4 D_3d5f4 (sp - 128 + 120) (U raw) ltac:(rewok W).
  zsd F_3d5f8 D_3d5f8 (sp - 128 + 112) (U (getr regs 8)) ltac:(rewok W).
  zsd F_3d5fc D_3d5fc (sp - 128 + 104) (U (getr regs 9)) ltac:(rewok W).
  zsd F_3d600 D_3d600 (sp - 128 + 96) (U (getr regs 18)) ltac:(rewok W).
  zsd F_3d604 D_3d604 (sp - 128 + 88) (U (getr regs 19)) ltac:(rewok W).
  zsd F_3d608 D_3d608 (sp - 128 + 80) (U (getr regs 20)) ltac:(rewok W).
  zsd F_3d60c D_3d60c (sp - 128 + 72) (U (getr regs 21)) ltac:(rewok W).
  zsd F_3d610 D_3d610 (sp - 128 + 64) (U (getr regs 22)) ltac:(rewok W).
  zsd F_3d614 D_3d614 (sp - 128 + 56) (U (getr regs 23)) ltac:(rewok W).
  zsd F_3d618 D_3d618 (sp - 128 + 48) (U (getr regs 24)) ltac:(rewok W).
  zsd F_3d61c D_3d61c (sp - 128 + 40) (U (getr regs 25)) ltac:(rewok W).
  zsd F_3d620 D_3d620 (sp - 128 + 32) (U (getr regs 26)) ltac:(rewok W).
  zsd F_3d624 D_3d624 (sp - 128 + 24) (U (getr regs 27)) ltac:(rewok W).
  zstep F_3d628 D_3d628. zstep F_3d62c D_3d62c. zstep F_3d630 D_3d630. zstep F_3d634 D_3d634. zstep F_3d638 D_3d638. zstep F_3d63c D_3d63c.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => set (Mf := X) end.
  assert (Ci' : cellA Mf 0xdf418 1 1) by (unfold Mf; unfold apart in *; recell Ci).
  assert (Cr' : cellA Mf 0x1609a2 1 0) by (unfold Mf; unfold apart in *; recell Cr).
  assert (R1' : cellA Mf 0x103e8 8 0x218a392cd3d5dbf) by (unfold Mf; unfold apart in *; recell R1).
  assert (R2' : cellA Mf 0x1045c 1 3) by (unfold Mf; unfold apart in *; recell R2).
  stepn F_3d640 D_3d640.
  zcall (art_asan_inited_fn _ _ _ _).
  zbft F_3d644 D_3d644.
  stepn F_3d648 D_3d648.
  zcall (art_rss_limit_fn _ _ _ _).
  zbft F_3d64c D_3d64c.
  zbft F_3d650 D_3d650.
  zstep F_3d654 D_3d654.
  zbtk F_3d658 D_3d658.
  zstep F_3d694 D_3d694. zstep F_3d698 D_3d698.
  zbtk F_3d69c D_3d69c.
  zstep F_3d6a4 D_3d6a4. zstep F_3d6a8 D_3d6a8.
  zbft F_3d6ac D_3d6ac.
  zstep F_3d6b0 D_3d6b0. zld F_3d6b4 D_3d6b4 0x103e8 R1'.
  zstep F_3d6b8 D_3d6b8. zstep F_3d6bc D_3d6bc. zstep F_3d6c0 D_3d6c0. zstep F_3d6c4 D_3d6c4. zstep F_3d6c8 D_3d6c8. zstep F_3d6cc D_3d6cc.
  zstep F_3d6d0 D_3d6d0.
  zlbu F_3d6d4 D_3d6d4 0x1045c R2'.
  zstep F_3d6d8 D_3d6d8. zstep F_3d6dc D_3d6dc. zstep F_3d6e0 D_3d6e0. zstep F_3d6e4 D_3d6e4.
  zbtk F_3d6e8 D_3d6e8.
  zstep F_3d668 D_3d668. zstep F_3d66c D_3d66c. zstep F_3d670 D_3d670.
  zbft F_3d674 D_3d674.
  zstep F_3d678 D_3d678. zstep F_3d67c D_3d67c.
  zsd F_3d680 D_3d680 (sp - 128 + 8) 1 ltac:(unfold Mf; rewok W).
  zsd F_3d684 D_3d684 (sp - 128 + 16) 16 ltac:(unfold Mf; rewok W).
  unfold Mf, art_alloc_memA1. zret.
Qed.

(* [comment removed for export] *)
Lemma art_alloc_ladder : forall regs (M rom : word -> option byte) (n : Z),
  getr regs 10 = Z_to_bv 64 49 -> getr regs 21 = Z_to_bv 64 n -> 1 <= n < 2 ^ 40 ->
  exists regs',
    msteps ASEGS (mkst regs (0x3d688 : word) M rom) (mkst regs' (0x3d75c : word) M rom)
    /\ getr regs' 19 = Z_to_bv 64 (AsanTab.rz_log n)
    /\ (forall r : reg, r <> 10%bv -> r <> 19%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom n H10 H21 Hn.
  unfold AsanTab.rz_log.
  destruct (Z.le_gt_cases n 48) as [C0|C0'].
  { eexists. split; [|split]; [ zbft F_3d688 D_3d688; zstep F_3d68c D_3d68c; stepn F_3d690 D_3d690; apply mst_refl | gres; zif; reflexivity | intros; kept_solve ]. }
  destruct (Z.le_gt_cases n 96) as [C1|C1'].
  { eexists. split; [|split]; [ zbtk F_3d688 D_3d688; zstep F_3d6f0 D_3d6f0; zbft F_3d6f4 D_3d6f4; zstep F_3d6f8 D_3d6f8; stepn F_3d6fc D_3d6fc; apply mst_refl
    | gres; zif; reflexivity | intros; kept_solve ]. }
  destruct (Z.le_gt_cases n 448) as [C2|C2'].
  { eexists. split; [|split]; [ zbtk F_3d688 D_3d688; zstep F_3d6f0 D_3d6f0; zbtk F_3d6f4 D_3d6f4; zstep F_3d700 D_3d700; zbft F_3d704 D_3d704; zstep F_3d708 D_3d708;
      stepn F_3d70c D_3d70c; apply mst_refl | gres; zif; reflexivity | intros; kept_solve ]. }
  destruct (Z.le_gt_cases n 3968) as [C3|C3'].
  { eexists. split; [|split]; [ zbtk F_3d688 D_3d688; zstep F_3d6f0 D_3d6f0; zbtk F_3d6f4 D_3d6f4; zstep F_3d700 D_3d700; zbtk F_3d704 D_3d704;
      zstep F_3d710 D_3d710; zstep F_3d714 D_3d714; zbft F_3d718 D_3d718; zstep F_3d71c D_3d71c; stepn F_3d720 D_3d720; apply mst_refl
    | gres; zif; reflexivity | intros; kept_solve ]. }
  destruct (Z.le_gt_cases n 16128) as [C4|C4'].
  { eexists. split; [|split]; [ zbtk F_3d688 D_3d688; zstep F_3d6f0 D_3d6f0; zbtk F_3d6f4 D_3d6f4; zstep F_3d700 D_3d700; zbtk F_3d704 D_3d704;
      zstep F_3d710 D_3d710; zstep F_3d714 D_3d714; zbtk F_3d718 D_3d718; zstep F_3d724 D_3d724; zstep F_3d728 D_3d728; zbft F_3d72c D_3d72c;
      zstep F_3d730 D_3d730; stepn F_3d734 D_3d734; apply mst_refl
    | gres; zif; reflexivity | intros; kept_solve ]. }
  destruct (Z.le_gt_cases n 32256) as [C5|C5'].
  { eexists. split; [|split]; [ zbtk F_3d688 D_3d688; zstep F_3d6f0 D_3d6f0; zbtk F_3d6f4 D_3d6f4; zstep F_3d700 D_3d700; zbtk F_3d704 D_3d704;
      zstep F_3d710 D_3d710; zstep F_3d714 D_3d714; zbtk F_3d718 D_3d718; zstep F_3d724 D_3d724; zstep F_3d728 D_3d728; zbtk F_3d72c D_3d72c;
      zstep F_3d738 D_3d738; zstep F_3d73c D_3d73c; zbft F_3d740 D_3d740; zstep F_3d744 D_3d744; stepn F_3d748 D_3d748; apply mst_refl
    | gres; zif; reflexivity | intros; kept_solve ]. }
  (* [comment removed for export] *)
  eexists. split; [|split]; [ zbtk F_3d688 D_3d688; zstep F_3d6f0 D_3d6f0; zbtk F_3d6f4 D_3d6f4; zstep F_3d700 D_3d700; zbtk F_3d704 D_3d704;
      zstep F_3d710 D_3d710; zstep F_3d714 D_3d714; zbtk F_3d718 D_3d718; zstep F_3d724 D_3d724; zstep F_3d728 D_3d728; zbtk F_3d72c D_3d72c;
      zstep F_3d738 D_3d738; zstep F_3d73c D_3d73c; zbtk F_3d740 D_3d740; zstep F_3d74c D_3d74c; zstep F_3d750 D_3d750; zstep F_3d754 D_3d754;
      zstep F_3d758 D_3d758; apply mst_refl
    | gres | intros; kept_solve ].
  destruct (Z.le_gt_cases n 64512) as [C6|C6']; zif; vals_lit; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma art_alloc_a2_fn : forall regs (M rom : word -> option byte) (sp ia : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 26 = Z_to_bv 64 (ia + 2047) ->
  16 <= sp -> sp < 2 ^ 64 -> 4096 <= ia -> ia + 4096 <= 0x634000 ->
  wrA M (sp - 16) 16 -> 0x634000 + 16 <= sp ->
  art_rz_rodata M -> cellA M (ia + 3624) 2 16 -> cellA M (ia + 3626) 2 2048 ->
  msteps ASEGS (mkst regs (0x3d75c : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x3d788 : bv 64)%bv) 2 (Z_to_bv 64 sp)) 9 (Z_to_bv 64 0)) 10 (Z_to_bv 64 7)) 11 (Z_to_bv 64 7)) 12 (Z_to_bv 64 11)) 13 (Z_to_bv 64 2048)) 14 (Z_to_bv 64 2048)) 20 (Z_to_bv 64 65536)) 24 (Z_to_bv 64 65535)) (0x3d788 : word) (Wn 8 (Wn 8 M (sp - 8) 0x3d774) (sp - 8) 0x3d788) rom).
Proof.
  intros regs M rom sp ia H2 H26 Hsp Hsp' Hia Hia' W IMG RO Cmin Cmax.
  zlh F_3d75c D_3d75c (ia + 3624) Cmin.
  stepfence F_3d760 D_3d760.
  zstep F_3d764 D_3d764. zstep F_3d768 D_3d768. zstep F_3d76c D_3d76c.
  stepn F_3d770 D_3d770.
  zcall (art_rz2log_16_fn _ _ _ sp _).
  zstep F_3d774 D_3d774.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cmax' : cellA X (ia + 3626) 2 2048) by (unfold apart in *; recell Cmax) end.
  zlh F_3d778 D_3d778 (ia + 3626) Cmax'.
  stepfence F_3d77c D_3d77c.
  zstep F_3d780 D_3d780.
  stepn F_3d784 D_3d784.
  zcall (art_rz2log_2048_fn _ _ _ sp _).
  { destruct RO as (R1 & R2 & R3). unfold art_rz_rodata. repeat split; recell R1 || recell R2 || recell R3. }
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_alloc_clamp : forall regs (M rom : word -> option byte) (n r : Z),
  getr regs 9 = Z_to_bv 64 0 -> getr regs 10 = Z_to_bv 64 7 -> getr regs 19 = Z_to_bv 64 r -> getr regs 21 = Z_to_bv 64 n ->
  1 <= n < 2 ^ 40 -> r = AsanTab.rz_log n ->
  exists regs',
    msteps ASEGS (mkst regs (0x3d788 : word) M rom) (mkst regs' (0x3d7a4 : word) M rom)
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
        [ zbft F_3d788 D_3d788; zstep F_3d78c D_3d78c; zbft F_3d790 D_3d790; zstep F_3d794 D_3d794; zstep F_3d798 D_3d798; zbft F_3d79c D_3d79c; zstep F_3d7a0 D_3d7a0; apply mst_refl
        | gres; f_equal; lia | gres; reflexivity | gres; rwH; f_equal; lia | intros; kept_solve ].
    + eexists. split; [|split; [|split; [|split]]];
        [ zbft F_3d788 D_3d788; zstep F_3d78c D_3d78c; zbft F_3d790 D_3d790; zstep F_3d794 D_3d794; zstep F_3d798 D_3d798; zbtk F_3d79c D_3d79c; apply mst_refl
        | gres; rwH; f_equal; lia | gres; reflexivity | gres; rwH; f_equal; lia | intros; kept_solve ].
  - specialize (Rlo ltac:(lia)).
    eexists. split; [|split; [|split; [|split]]];
      [ zbtk F_3d788 D_3d788; zbtk F_3d834 D_3d834; zstep F_3d794 D_3d794; zstep F_3d798 D_3d798; zbtk F_3d79c D_3d79c; apply mst_refl
      | gres; rwH; f_equal; lia | gres; reflexivity | gres; rwH; reflexivity | intros; kept_solve ].
  - specialize (R7 RS).
    eexists. split; [|split; [|split; [|split]]];
      [ zbtk F_3d788 D_3d788; zbft F_3d834 D_3d834; zstep F_3d838 D_3d838; zstep F_3d83c D_3d83c; zstep F_3d840 D_3d840; zbft F_3d844 D_3d844;
        stepn F_3d848 D_3d848; apply mst_refl
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
  16 <= sp -> sp < 2 ^ 64 -> 4096 <= ia -> ia + 4096 <= 0x634000 -> 0x634000 + 16 <= sp ->
  1 <= n < 2 ^ 40 -> 0 <= r <= 7 -> rs = (Z.max n 8 + 7) / 8 * 8 -> rz = 16 * 2 ^ r -> rs + rz <= 65536 ->
  wrA M (sp - 16) 16 -> cellA M (ia + 3616) 8 (2 ^ 40) -> art_tsd M tp key tsd ctx t -> 1 <= t ->
  apart (sp - 16) 16 (tp - 88) 8 -> apart (sp - 16) 16 (tsd + 8 * key) 8 -> apart (sp - 16) 16 (ctx + 152) 8 ->
  msteps ASEGS (mkst regs (0x3d7a4 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x3d890 : bv 64)%bv) 2 (Z_to_bv 64 sp)) 8 (Z_to_bv 64 1)) 9 (Z_to_bv 64 n)) 10 (Z_to_bv 64 ia)) 11 (Z_to_bv 64 (t + 208))) 12 (Z_to_bv 64 (rs + rz))) 13 (Z_to_bv 64 8)) 19 (Z_to_bv 64 (rs + rz))) 20 (Z_to_bv 64 rz)) 24 (Z_to_bv 64 (2 ^ 64 - 8))) 26 (Z_to_bv 64 t)) (0x41d48 : word) (Wn 8 M (sp - 8) 0x3d874) rom).
Proof.
  intros regs M rom sp ia n r rs rz tp key tsd ctx t H2 H4 H8 H10 H18 H19 H20 H21 H22 H26 Hsp Hsp' Hia Hia' IMG Hn Hr Hrs Hrz Hprim W Cmax TSD Ht A1 A2 A3.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  assert (Hrs8 : rs mod 8 = 0) by (subst rs; apply Z_mod_mult).
  assert (Hrslo : 8 <= rs). { subst rs. pose proof (Z.mul_succ_div_gt (Z.max n 8 + 7) 8 ltac:(lia)). pose proof (Z.mul_div_le (Z.max n 8 + 7) 8 ltac:(lia)). lia. } assert (Hrz16 : 16 <= rz <= 2048) by (subst rz; split; [|change 2048 with (16 * 2 ^ 7); apply Z.mul_le_mono_nonneg_l; [lia|apply Z.pow_le_mono_r; lia]]; pose proof (Z.pow_pos_nonneg 2 r); nia).
  zstep F_3d7a4 D_3d7a4. zstep F_3d7a8 D_3d7a8. zstep F_3d7ac D_3d7ac. zstep F_3d7b0 D_3d7b0. zstep F_3d7b4 D_3d7b4.
  stepn F_3d7b8 D_3d7b8. rwH. rewrite art_zb_and by lia. rewrite art_land_m8 by lia.
  match goal with |- context [Z_to_bv 64 (?e / 8 * 8)] => replace (e / 8 * 8) with rs by (rewrite Hrs; f_equal; f_equal; lia) end.
  zstep F_3d7bc D_3d7bc. zstep F_3d7c0 D_3d7c0.
  stepn F_3d7c4 D_3d7c4. rwH. rewrite art_zb_andi by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8. rewrite Hrs8.
  zbft F_3d7c8 D_3d7c8.
  zstep F_3d7cc D_3d7cc. zstep F_3d7d0 D_3d7d0. zstep F_3d7d4 D_3d7d4.
  stepn F_3d7d8 D_3d7d8. rwH. rewrite art_zb_sllw_small by (subst rz; lia). rewrite <- Hrz.
  zstep F_3d7dc D_3d7dc. zstep F_3d7e0 D_3d7e0. zstep F_3d7e4 D_3d7e4. zstep F_3d7e8 D_3d7e8. zstep F_3d7ec D_3d7ec. zstep F_3d7f0 D_3d7f0.
  zstep F_3d7f4 D_3d7f4.
  stepn F_3d7f8 D_3d7f8. rwH. rewrite art_zb_and by lia. rewrite Z.land_0_l.
  zstep F_3d7fc D_3d7fc. zstep F_3d800 D_3d800.
  zbft F_3d804 D_3d804. zbft F_3d808 D_3d808.
  zld F_3d80c D_3d80c (ia + 3616) Cmax.
  zbtk F_3d810 D_3d810.
  stepn F_3d870 D_3d870.
  zcall (art_cur_thread_fn _ _ _ _ sp tp key tsd ctx t).
  zbft F_3d878 D_3d878 || (zstep F_3d874 D_3d874; zbft F_3d878 D_3d878).
  zstep F_3d87c D_3d87c. zstep F_3d880 D_3d880. zstep F_3d884 D_3d884. zstep F_3d888 D_3d888.
  stepn F_3d88c D_3d88c.
  zret.
Qed.
End FPX.
