(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac ArtLeaf ArtPoison ArtAllocC ArtAllocD ArtAllocV.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import As0_code_3d034_3dfbc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section FPX. Context {fx : PropExec.FPState}.

Lemma art_alloc_d1_any : forall regs (M rom : word -> option byte) (ab n rz : Z),
  getr regs 9 = Z_to_bv 64 n -> getr regs 20 = Z_to_bv 64 (ab + rz) -> getr regs 22 = Z_to_bv 64 (n / 8 * 8) ->
  4096 <= ab -> ab + rz + n < 2 ^ 47 -> (ab + rz + n < SB \/ kHighMemBeg <= ab) -> 16 <= rz <= 2048 -> 8 <= n < 2 ^ 40 ->
  art_layout M -> cellA M (0xdb338 + 85) 1 1 -> (n mod 8 <> 0 -> wrA M (art_d1_addr ab rz n) 1) ->
  exists regs',
    msteps ASEGS (mkst regs (0x3d828 : word) M rom) (mkst regs' (0x3d8bc : word) (art_d1_mem M ab rz n) rom)
    /\ (forall r : reg, art_d1_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom ab n rz H9 H20 H22 Hab Hab' MEM Hrz Hn L Cpp Wsh.
  unfold art_d1_mem, art_d1_addr in *.
  destruct (Z.eqb_spec (n mod 8) 0) as [E|NE].
  - exists regs. split; [|intros r _; reflexivity].
    apply (art_alloc_d1_none regs M rom n H9 H22 ltac:(lia) E).
  - specialize (Wsh NE). unfold SB, kHighMemBeg in MEM.
    pose proof L as (G48 & Csb & G50 & Cmb & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
    pose proof (Z.mul_div_le n 8 ltac:(lia)) as D1. pose proof (Z.mul_succ_div_gt n 8 ltac:(lia)) as D2.
    pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as D3. pose proof (Z.div_mod n 8 ltac:(lia)) as D4.
    assert (D5 : n / 8 * 8 <> n) by lia.
    destruct MEM as [LO|HI].
    + eexists. split.
      * zbft F_3d828 D_3d828.
        stepn F_3d82c D_3d82c.
        zcall (art_can_poison_fn _ _ _ _).
        zbft F_3d830 D_3d830.
        zstep F_3d834 D_3d834. zld F_3d838 D_3d838 0xd58b8 G48. zld F_3d83c D_3d83c 0xddb38 Csb. unfold SB.
        zstep F_3d840 D_3d840. zstep F_3d844 D_3d844. zstep F_3d848 D_3d848. zstep F_3d84c D_3d84c. zstep F_3d850 D_3d850.
        zbtk F_3d854 D_3d854.
        zstep F_3d898 D_3d898. zld F_3d89c D_3d89c 0xd58b0 G40.
        zlbu F_3d8a0 D_3d8a0 (0xdb338 + 85) Cpp.
        stepn F_3d8a4 D_3d8a4. rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
        zstep F_3d8a8 D_3d8a8. zstep F_3d8ac D_3d8ac.
        stepn F_3d8b0 D_3d8b0. rwH. rewrite art_zb_and by lia. rewrite art_land_full_r by lia.
        stepn F_3d8b4 D_3d8b4. rwH. rewrite art_zb_andi by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
        zsb F_3d8b8 D_3d8b8 (2147450880 + (ab + rz + n / 8 * 8) / 8) (n mod 8) ltac:(rewok Wsh).
        apply mst_refl.
      * intros r Hr. unfold art_d1_kept in Hr. decompose [and] Hr. kept_solve.
    + eexists. split.
      * zbft F_3d828 D_3d828.
        stepn F_3d82c D_3d82c.
        zcall (art_can_poison_fn _ _ _ _).
        zbft F_3d830 D_3d830.
        zstep F_3d834 D_3d834. zld F_3d838 D_3d838 0xd58b8 G48. zld F_3d83c D_3d83c 0xddb38 Csb. unfold SB.
        zstep F_3d840 D_3d840. zstep F_3d844 D_3d844. zstep F_3d848 D_3d848. zstep F_3d84c D_3d84c. zstep F_3d850 D_3d850.
        zbft F_3d854 D_3d854.
        zstep F_3d858 D_3d858. zld F_3d85c D_3d85c 0xd58c0 G50. zstep F_3d860 D_3d860. zld F_3d864 D_3d864 0xd58c8 G58.
        zld F_3d868 D_3d868 0xde828 Cmb. zld F_3d86c D_3d86c 0xde830 Cme.
        zstep F_3d870 D_3d870.
        zbtk F_3d874 D_3d874.
        zstep F_3d87c D_3d87c. zld F_3d880 D_3d880 0xd58d0 G60. zld F_3d884 D_3d884 0xde820 Che. unfold kHighMemEnd.
        zstep F_3d888 D_3d888. zstep F_3d88c D_3d88c.
        zbft F_3d890 D_3d890. zbft F_3d894 D_3d894.
        zstep F_3d898 D_3d898. zld F_3d89c D_3d89c 0xd58b0 G40.
        zlbu F_3d8a0 D_3d8a0 (0xdb338 + 85) Cpp.
        stepn F_3d8a4 D_3d8a4. rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
        zstep F_3d8a8 D_3d8a8. zstep F_3d8ac D_3d8ac.
        stepn F_3d8b0 D_3d8b0. rwH. rewrite art_zb_and by lia. rewrite art_land_full_r by lia.
        stepn F_3d8b4 D_3d8b4. rwH. rewrite art_zb_andi by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
        zsb F_3d8b8 D_3d8b8 (2147450880 + (ab + rz + n / 8 * 8) / 8) (n mod 8) ltac:(rewok Wsh).
        apply mst_refl.
      * intros r Hr. unfold art_d1_kept in Hr. decompose [and] Hr. kept_solve.
Qed.

Definition art_d2_large_mem (M : word -> option byte) (sp t n nd mc mb mr ml : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) 0x3d8c0) (sp - 24) 0x689bc) (t + 2800) (mc + 1)) (t + 2800 + 8) (mb + n)) (t + 2800 + 16) (mr + (nd - n)))
       (t + 2800 + 104) (ml + 1).

Definition art_d2_kept (r : reg) : Prop :=
  r <> 1%bv /\ r <> 10%bv /\ r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv.

Lemma art_alloc_d2_large_fn : forall regs (M rom : word -> option byte) (sp ab n nd rz tp key tsd ctx t mc mb mr ml : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> getr regs 9 = Z_to_bv 64 n -> getr regs 19 = Z_to_bv 64 nd -> getr regs 20 = Z_to_bv 64 (ab + rz) ->
  32 <= sp -> sp + 128 < 2 ^ 64 -> 0x633000 + 32 <= sp -> 4096 <= n -> n <= nd -> 65536 < nd < 2 ^ 40 -> 0 <= ab + rz < 2 ^ 64 ->
  0 <= mc < 2 ^ 64 -> 0 <= mb < 2 ^ 64 -> 0 <= mr < 2 ^ 64 -> 0 <= ml < 2 ^ 64 ->
  wrA M (sp - 32) 32 -> art_tsd M tp key tsd ctx t -> 4096 <= t -> t + 4096 < 2 ^ 64 -> (t + 4096 <= 0x10000 \/ 0x633000 <= t) ->
  apart (sp - 32) 32 0xdd3a0 8 -> apart (sp - 32) 32 (tp - 88) 8 -> apart (sp - 32) 32 (tsd + 8 * key) 8 -> apart (sp - 32) 32 (ctx + 152) 8 ->
  apart (sp - 32) 160 (t + 2800) 112 ->
  cellA M (t + 2800) 8 mc -> cellA M (t + 2800 + 8) 8 mb -> cellA M (t + 2800 + 16) 8 mr -> cellA M (t + 2800 + 104) 8 ml -> wrA M (t + 2800) 112 ->
  cellA M (sp + 8) 8 1 -> art_layout M -> cellA M (0xdb338 + 44) 4 4096 -> cellA M (0xdb338 + 52) 4 190 ->
  exists regs',
    msteps ASEGS (mkst regs (0x3d8bc : word) M rom) (mkst regs' (0xcbb2c : word) (art_d2_large_mem M sp t n nd mc mb mr ml) rom)
    /\ getr regs' 1 = (0x3da50 : bv 64)%bv /\ getr regs' 10 = Z_to_bv 64 (ab + rz) /\ getr regs' 11 = Z_to_bv 64 190 /\ getr regs' 12 = Z_to_bv 64 4096
    /\ (forall r : reg, art_d2_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp ab n nd rz tp key tsd ctx t mc mb mr ml H2 H4 H9 H19 H20 Hsp Hsp' IMG Hn Hnd Hnd' Hub Hmc Hmb Hmr Hml
         W TSD Ht Ht' Timg A1 A2 A3 A4 A5 Cmc Cmb Cmr Cml Wts Ccf L Cmax Cfb.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  pose proof L as (G48 & Csb & G50 & Cmb0 & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
  unfold art_d2_large_mem.
  eexists. split; [|split; [|split; [|split; [|split]]]].
  - stepn F_3d8bc D_3d8bc.
    zcall (art_thread_stats_fn _ _ _ _ sp tp key tsd ctx t).
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (Cmc' : cellA X (t + 2800) 8 mc) by (unfold apart in *; recell Cmc);
      assert (Cmb' : cellA X (t + 2800 + 8) 8 mb) by (unfold apart in *; recell Cmb);
      assert (Cmr' : cellA X (t + 2800 + 16) 8 mr) by (unfold apart in *; recell Cmr);
      assert (Wts' : wrA X (t + 2800) 112) by (repeat apply wr_Wn; exact Wts) end.
    zld F_3d8c0 D_3d8c0 (t + 2800 + 16) Cmr'.
    zld F_3d8c4 D_3d8c4 (t + 2800) Cmc'.
    zld F_3d8c8 D_3d8c8 (t + 2800 + 8) Cmb'.
    zstep F_3d8cc D_3d8cc. zstep F_3d8d0 D_3d8d0. zstep F_3d8d4 D_3d8d4. zstep F_3d8d8 D_3d8d8. zstep F_3d8dc D_3d8dc. zstep F_3d8e0 D_3d8e0.
    zsd F_3d8e4 D_3d8e4 (t + 2800) (mc + 1) ltac:(rewok Wts').
    zsd F_3d8e8 D_3d8e8 (t + 2800 + 8) (mb + n) ltac:(rewok Wts').
    zsd F_3d8ec D_3d8ec (t + 2800 + 16) (mr + (nd - n)) ltac:(rewok Wts').
    zbft F_3d8f0 D_3d8f0.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cml' : cellA X (t + 2800 + 104) 8 ml) by (unfold apart in *; recell Cml) end.
    zld F_3d8f4 D_3d8f4 (t + 2800 + 104) Cml'.
    zstep F_3d8f8 D_3d8f8.
    zsd F_3d8fc D_3d8fc (t + 2800 + 104) (ml + 1) ltac:(rewok Wts').
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (Ccf' : cellA X (sp + 8) 8 1) by (unfold apart in *; recell Ccf);
      assert (G40' : cellA X 0xd58b0 8 0xdb338) by (unfold apart in *; recell G40);
      assert (Cmax' : cellA X (0xdb338 + 44) 4 4096) by (unfold apart in *; recell Cmax);
      assert (G68' : cellA X 0xd58d8 8 0xd7818) by (unfold apart in *; recell G68);
      assert (Crm' : cellA X 0xd7818 8 0xcbb2c) by (unfold apart in *; recell Crm);
      assert (Cfb' : cellA X (0xdb338 + 52) 4 190) by (unfold apart in *; recell Cfb) end.
    zld F_3d900 D_3d900 (sp + 8) Ccf'.
    zbtk F_3d904 D_3d904.
    zstep F_3da1c D_3da1c. zld F_3da20 D_3da20 0xd58b0 G40'.
    zlw F_3da24 D_3da24 (0xdb338 + 44) Cmax'.
    zbft F_3da28 D_3da28.
    zstep F_3da2c D_3da2c.
    zbft F_3da30 D_3da30.
    zstep F_3da34 D_3da34.
    zstep F_3da38 D_3da38. zld F_3da3c D_3da3c 0xd58d8 G68'. zld F_3da40 D_3da40 0xd7818 Crm'.
    zlw F_3da44 D_3da44 (0xdb338 + 52) Cfb'.
    zstep F_3da48 D_3da48.
    stepjr F_3da4c D_3da4c (0xcbb2c : bv 64)%bv ltac:(gres; bveq).
    apply mst_refl.
  - gres. apply bv_eq. reflexivity.
  - kept_solve.
  - kept_solve.
  - kept_solve.
  - intros r Hr. unfold art_d2_kept in Hr. decompose [and] Hr. kept_solve.
Qed.
End FPX.
