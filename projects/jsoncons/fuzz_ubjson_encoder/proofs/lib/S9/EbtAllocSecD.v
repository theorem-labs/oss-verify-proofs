(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import As0Tables.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import ArtMem ArtRegs ArtAtomics ArtTac EbtLeaf EbtPoison EbtAllocC EbtAllocD EbtAllocV.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_r3cf10_3de98.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_alloc_d1_any : forall regs (M rom : word -> option byte) (ab n rz : Z),
  getr regs 9 = Z_to_bv 64 n -> getr regs 20 = Z_to_bv 64 (ab + rz) -> getr regs 22 = Z_to_bv 64 (n / 8 * 8) ->
  4096 <= ab -> ab + rz + n < 2 ^ 47 -> (ab + rz + n < SB \/ kHighMemBeg <= ab) -> 16 <= rz <= 2048 -> 8 <= n < 2 ^ 40 ->
  art_layout M -> cellA M (0x1438f8 + 85) 1 1 -> (n mod 8 <> 0 -> wrA M (art_d1_addr ab rz n) 1) ->
  exists regs',
    msteps ASEGS (mkst regs (0x53aac : word) M rom) (mkst regs' (0x53b40 : word) (art_d1_mem M ab rz n) rom)
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
      * zbft F_53a5c D_53a5c.
        stepn F_53a60 D_53a60.
        zcall (art_can_poison_fn _ _ _ _).
        zbft F_53a64 D_53a64.
        zstep F_53a68 D_53a68. zld F_53a6c D_53a6c 0x13d8c8 G48. zld F_53a70 D_53a70 0x1460f8 Csb. unfold SB.
        zstep F_53a74 D_53a74. zstep F_53a78 D_53a78. zstep F_53a7c D_53a7c. zstep F_53a80 D_53a80. zstep F_53a84 D_53a84.
        zbtk F_53a88 D_53a88.
        zstep F_53acc D_53acc. zld F_53ad0 D_53ad0 0x13d8c0 G40.
        zlbu F_53ad4 D_53ad4 (0x1438f8 + 85) Cpp.
        stepn F_53ad8 D_53ad8. rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
        zstep F_53adc D_53adc. zstep F_53ae0 D_53ae0.
        stepn F_53ae4 D_53ae4. rwH. rewrite art_zb_and by lia. rewrite art_land_full_r by lia.
        stepn F_53ae8 D_53ae8. rwH. rewrite art_zb_andi by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
        zsb F_53aec D_53aec (2147450880 + (ab + rz + n / 8 * 8) / 8) (n mod 8) ltac:(rewok Wsh).
        apply mst_refl.
      * intros r Hr. unfold art_d1_kept in Hr. decompose [and] Hr. kept_solve.
    + eexists. split.
      * zbft F_53a5c D_53a5c.
        stepn F_53a60 D_53a60.
        zcall (art_can_poison_fn _ _ _ _).
        zbft F_53a64 D_53a64.
        zstep F_53a68 D_53a68. zld F_53a6c D_53a6c 0x13d8c8 G48. zld F_53a70 D_53a70 0x1460f8 Csb. unfold SB.
        zstep F_53a74 D_53a74. zstep F_53a78 D_53a78. zstep F_53a7c D_53a7c. zstep F_53a80 D_53a80. zstep F_53a84 D_53a84.
        zbft F_53a88 D_53a88.
        zstep F_53a8c D_53a8c. zld F_53a90 D_53a90 0x13d8d0 G50. zstep F_53a94 D_53a94. zld F_53a98 D_53a98 0x13d8d8 G58.
        zld F_53a9c D_53a9c 0x146de8 Cmb. zld F_53aa0 D_53aa0 0x146df0 Cme.
        zstep F_53aa4 D_53aa4.
        zbtk F_53aa8 D_53aa8.
        zstep F_53ab0 D_53ab0. zld F_53ab4 D_53ab4 0x13d8e0 G60. zld F_53ab8 D_53ab8 0x146de0 Che. unfold kHighMemEnd.
        zstep F_53abc D_53abc. zstep F_53ac0 D_53ac0.
        zbft F_53ac4 D_53ac4. zbft F_53ac8 D_53ac8.
        zstep F_53acc D_53acc. zld F_53ad0 D_53ad0 0x13d8c0 G40.
        zlbu F_53ad4 D_53ad4 (0x1438f8 + 85) Cpp.
        stepn F_53ad8 D_53ad8. rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
        zstep F_53adc D_53adc. zstep F_53ae0 D_53ae0.
        stepn F_53ae4 D_53ae4. rwH. rewrite art_zb_and by lia. rewrite art_land_full_r by lia.
        stepn F_53ae8 D_53ae8. rwH. rewrite art_zb_andi by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
        zsb F_53aec D_53aec (2147450880 + (ab + rz + n / 8 * 8) / 8) (n mod 8) ltac:(rewok Wsh).
        apply mst_refl.
      * intros r Hr. unfold art_d1_kept in Hr. decompose [and] Hr. kept_solve.
Qed.

Definition art_d2_large_mem (M : word -> option byte) (sp t n nd mc mb mr ml : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) 0x53b44) (sp - 24) 0x83c68) (t + 2800) (mc + 1)) (t + 2800 + 8) (mb + n)) (t + 2800 + 16) (mr + (nd - n)))
       (t + 2800 + 104) (ml + 1).

Definition art_d2_kept (r : reg) : Prop :=
  r <> 1%bv /\ r <> 10%bv /\ r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv.

#[using="Type"] Lemma art_alloc_d2_large_fn : forall regs (M rom : word -> option byte) (sp ab n nd rz tp key tsd ctx t mc mb mr ml : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> getr regs 9 = Z_to_bv 64 n -> getr regs 19 = Z_to_bv 64 nd -> getr regs 20 = Z_to_bv 64 (ab + rz) ->
  32 <= sp -> sp + 128 < 2 ^ 64 -> 0x69c000 + 32 <= sp -> 4096 <= n -> n <= nd -> 65536 < nd < 2 ^ 40 -> 0 <= ab + rz < 2 ^ 64 ->
  0 <= mc < 2 ^ 64 -> 0 <= mb < 2 ^ 64 -> 0 <= mr < 2 ^ 64 -> 0 <= ml < 2 ^ 64 ->
  wrA M (sp - 32) 32 -> art_tsd M tp key tsd ctx t -> 4096 <= t -> t + 4096 < 2 ^ 64 -> (t + 4096 <= 0x10000 \/ 0x69c000 <= t) ->
  apart (sp - 32) 32 0x145960 8 -> apart (sp - 32) 32 (tp - 88) 8 -> apart (sp - 32) 32 (tsd + 8 * key) 8 -> apart (sp - 32) 32 (ctx + 152) 8 ->
  apart (sp - 32) 160 (t + 2800) 112 ->
  cellA M (t + 2800) 8 mc -> cellA M (t + 2800 + 8) 8 mb -> cellA M (t + 2800 + 16) 8 mr -> cellA M (t + 2800 + 104) 8 ml -> wrA M (t + 2800) 112 ->
  cellA M (sp + 8) 8 1 -> art_layout M -> cellA M (0x1438f8 + 44) 4 4096 -> cellA M (0x1438f8 + 52) 4 190 ->
  exists regs',
    msteps ASEGS (mkst regs (0x53b40 : word) M rom) (mkst regs' (0x130034 : word) (art_d2_large_mem M sp t n nd mc mb mr ml) rom)
    /\ getr regs' 1 = (0x53cd4 : bv 64)%bv /\ getr regs' 10 = Z_to_bv 64 (ab + rz) /\ getr regs' 11 = Z_to_bv 64 190 /\ getr regs' 12 = Z_to_bv 64 4096
    /\ (forall r : reg, art_d2_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp ab n nd rz tp key tsd ctx t mc mb mr ml H2 H4 H9 H19 H20 Hsp Hsp' IMG Hn Hnd Hnd' Hub Hmc Hmb Hmr Hml
         W TSD Ht Ht' Timg A1 A2 A3 A4 A5 Cmc Cmb Cmr Cml Wts Ccf L Cmax Cfb.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  pose proof L as (G48 & Csb & G50 & Cmb0 & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
  unfold art_d2_large_mem.
  eexists. split; [|split; [|split; [|split; [|split]]]].
  - stepn F_53af0 D_53af0.
    zcall (art_thread_stats_fn _ _ _ _ sp tp key tsd ctx t).
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (Cmc' : cellA X (t + 2800) 8 mc) by (unfold apart in *; recell Cmc);
      assert (Cmb' : cellA X (t + 2800 + 8) 8 mb) by (unfold apart in *; recell Cmb);
      assert (Cmr' : cellA X (t + 2800 + 16) 8 mr) by (unfold apart in *; recell Cmr);
      assert (Wts' : wrA X (t + 2800) 112) by (repeat apply wr_Wn; exact Wts) end.
    zld F_53af4 D_53af4 (t + 2800 + 16) Cmr'.
    zld F_53af8 D_53af8 (t + 2800) Cmc'.
    zld F_53afc D_53afc (t + 2800 + 8) Cmb'.
    zstep F_53b00 D_53b00. zstep F_53b04 D_53b04. zstep F_53b08 D_53b08. zstep F_53b0c D_53b0c. zstep F_53b10 D_53b10. zstep F_53b14 D_53b14.
    zsd F_53b18 D_53b18 (t + 2800) (mc + 1) ltac:(rewok Wts').
    zsd F_53b1c D_53b1c (t + 2800 + 8) (mb + n) ltac:(rewok Wts').
    zsd F_53b20 D_53b20 (t + 2800 + 16) (mr + (nd - n)) ltac:(rewok Wts').
    zbft F_53b24 D_53b24.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cml' : cellA X (t + 2800 + 104) 8 ml) by (unfold apart in *; recell Cml) end.
    zld F_53b28 D_53b28 (t + 2800 + 104) Cml'.
    zstep F_53b2c D_53b2c.
    zsd F_53b30 D_53b30 (t + 2800 + 104) (ml + 1) ltac:(rewok Wts').
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (Ccf' : cellA X (sp + 8) 8 1) by (unfold apart in *; recell Ccf);
      assert (G40' : cellA X 0x13d8c0 8 0x1438f8) by (unfold apart in *; recell G40);
      assert (Cmax' : cellA X (0x1438f8 + 44) 4 4096) by (unfold apart in *; recell Cmax);
      assert (G68' : cellA X 0x13d8e8 8 0x13f8d8) by (unfold apart in *; recell G68);
      assert (Crm' : cellA X 0x13f8d8 8 0x130034) by (unfold apart in *; recell Crm);
      assert (Cfb' : cellA X (0x1438f8 + 52) 4 190) by (unfold apart in *; recell Cfb) end.
    zld F_53b34 D_53b34 (sp + 8) Ccf'.
    zbtk F_53b38 D_53b38.
    zstep F_53c50 D_53c50. zld F_53c54 D_53c54 0x13d8c0 G40'.
    zlw F_53c58 D_53c58 (0x1438f8 + 44) Cmax'.
    zbft F_53c5c D_53c5c.
    zstep F_53c60 D_53c60.
    zbft F_53c64 D_53c64.
    zstep F_53c68 D_53c68.
    zstep F_53c6c D_53c6c. zld F_53c70 D_53c70 0x13d8e8 G68'. zld F_53c74 D_53c74 0x13f8d8 Crm'.
    zlw F_53c78 D_53c78 (0x1438f8 + 52) Cfb'.
    zstep F_53c7c D_53c7c.
    stepjr F_53c80 D_53c80 (0x130034 : bv 64)%bv ltac:(gres; bveq).
    apply mst_refl.
  - gres. apply bv_eq. reflexivity.
  - kept_solve.
  - kept_solve.
  - kept_solve.
  - intros r Hr. unfold art_d2_kept in Hr. decompose [and] Hr. kept_solve.
Qed.
End FPX.
