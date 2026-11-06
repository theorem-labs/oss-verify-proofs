(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import As0Tables.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import ArtMem ArtRegs ArtAtomics ArtTac EatLeaf EatPoison EatAllocC EatAllocD EatAllocV.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_r3cf10_3de98.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_alloc_d1_any : forall regs (M rom : word -> option byte) (ab n rz : Z),
  getr regs 9 = Z_to_bv 64 n -> getr regs 20 = Z_to_bv 64 (ab + rz) -> getr regs 22 = Z_to_bv 64 (n / 8 * 8) ->
  4096 <= ab -> ab + rz + n < 2 ^ 47 -> (ab + rz + n < SB \/ kHighMemBeg <= ab) -> 16 <= rz <= 2048 -> 8 <= n < 2 ^ 40 ->
  art_layout M -> cellA M (0x13f1f8 + 85) 1 1 -> (n mod 8 <> 0 -> wrA M (art_d1_addr ab rz n) 1) ->
  exists regs',
    msteps ASEGS (mkst regs (0x53284 : word) M rom) (mkst regs' (0x53318 : word) (art_d1_mem M ab rz n) rom)
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
      * zbft F_53234 D_53234.
        stepn F_53238 D_53238.
        zcall (art_can_poison_fn _ _ _ _).
        zbft F_5323c D_5323c.
        zstep F_53240 D_53240. zld F_53244 D_53244 0x1391b8 G48. zld F_53248 D_53248 0x1419f8 Csb. unfold SB.
        zstep F_5324c D_5324c. zstep F_53250 D_53250. zstep F_53254 D_53254. zstep F_53258 D_53258. zstep F_5325c D_5325c.
        zbtk F_53260 D_53260.
        zstep F_532a4 D_532a4. zld F_532a8 D_532a8 0x1391b0 G40.
        zlbu F_532ac D_532ac (0x13f1f8 + 85) Cpp.
        stepn F_532b0 D_532b0. rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
        zstep F_532b4 D_532b4. zstep F_532b8 D_532b8.
        stepn F_532bc D_532bc. rwH. rewrite art_zb_and by lia. rewrite art_land_full_r by lia.
        stepn F_532c0 D_532c0. rwH. rewrite art_zb_andi by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
        zsb F_532c4 D_532c4 (2147450880 + (ab + rz + n / 8 * 8) / 8) (n mod 8) ltac:(rewok Wsh).
        apply mst_refl.
      * intros r Hr. unfold art_d1_kept in Hr. decompose [and] Hr. kept_solve.
    + eexists. split.
      * zbft F_53234 D_53234.
        stepn F_53238 D_53238.
        zcall (art_can_poison_fn _ _ _ _).
        zbft F_5323c D_5323c.
        zstep F_53240 D_53240. zld F_53244 D_53244 0x1391b8 G48. zld F_53248 D_53248 0x1419f8 Csb. unfold SB.
        zstep F_5324c D_5324c. zstep F_53250 D_53250. zstep F_53254 D_53254. zstep F_53258 D_53258. zstep F_5325c D_5325c.
        zbft F_53260 D_53260.
        zstep F_53264 D_53264. zld F_53268 D_53268 0x1391c0 G50. zstep F_5326c D_5326c. zld F_53270 D_53270 0x1391c8 G58.
        zld F_53274 D_53274 0x1426e8 Cmb. zld F_53278 D_53278 0x1426f0 Cme.
        zstep F_5327c D_5327c.
        zbtk F_53280 D_53280.
        zstep F_53288 D_53288. zld F_5328c D_5328c 0x1391d0 G60. zld F_53290 D_53290 0x1426e0 Che. unfold kHighMemEnd.
        zstep F_53294 D_53294. zstep F_53298 D_53298.
        zbft F_5329c D_5329c. zbft F_532a0 D_532a0.
        zstep F_532a4 D_532a4. zld F_532a8 D_532a8 0x1391b0 G40.
        zlbu F_532ac D_532ac (0x13f1f8 + 85) Cpp.
        stepn F_532b0 D_532b0. rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
        zstep F_532b4 D_532b4. zstep F_532b8 D_532b8.
        stepn F_532bc D_532bc. rwH. rewrite art_zb_and by lia. rewrite art_land_full_r by lia.
        stepn F_532c0 D_532c0. rwH. rewrite art_zb_andi by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
        zsb F_532c4 D_532c4 (2147450880 + (ab + rz + n / 8 * 8) / 8) (n mod 8) ltac:(rewok Wsh).
        apply mst_refl.
      * intros r Hr. unfold art_d1_kept in Hr. decompose [and] Hr. kept_solve.
Qed.

Definition art_d2_large_mem (M : word -> option byte) (sp t n nd mc mb mr ml : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) 0x5331c) (sp - 24) 0x83440) (t + 2800) (mc + 1)) (t + 2800 + 8) (mb + n)) (t + 2800 + 16) (mr + (nd - n)))
       (t + 2800 + 104) (ml + 1).

Definition art_d2_kept (r : reg) : Prop :=
  r <> 1%bv /\ r <> 10%bv /\ r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv.

#[using="Type"] Lemma art_alloc_d2_large_fn : forall regs (M rom : word -> option byte) (sp ab n nd rz tp key tsd ctx t mc mb mr ml : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> getr regs 9 = Z_to_bv 64 n -> getr regs 19 = Z_to_bv 64 nd -> getr regs 20 = Z_to_bv 64 (ab + rz) ->
  32 <= sp -> sp + 128 < 2 ^ 64 -> 0x698000 + 32 <= sp -> 4096 <= n -> n <= nd -> 65536 < nd < 2 ^ 40 -> 0 <= ab + rz < 2 ^ 64 ->
  0 <= mc < 2 ^ 64 -> 0 <= mb < 2 ^ 64 -> 0 <= mr < 2 ^ 64 -> 0 <= ml < 2 ^ 64 ->
  wrA M (sp - 32) 32 -> art_tsd M tp key tsd ctx t -> 4096 <= t -> t + 4096 < 2 ^ 64 -> (t + 4096 <= 0x10000 \/ 0x698000 <= t) ->
  apart (sp - 32) 32 0x141260 8 -> apart (sp - 32) 32 (tp - 88) 8 -> apart (sp - 32) 32 (tsd + 8 * key) 8 -> apart (sp - 32) 32 (ctx + 152) 8 ->
  apart (sp - 32) 160 (t + 2800) 112 ->
  cellA M (t + 2800) 8 mc -> cellA M (t + 2800 + 8) 8 mb -> cellA M (t + 2800 + 16) 8 mr -> cellA M (t + 2800 + 104) 8 ml -> wrA M (t + 2800) 112 ->
  cellA M (sp + 8) 8 1 -> art_layout M -> cellA M (0x13f1f8 + 44) 4 4096 -> cellA M (0x13f1f8 + 52) 4 190 ->
  exists regs',
    msteps ASEGS (mkst regs (0x53318 : word) M rom) (mkst regs' (0x12b88c : word) (art_d2_large_mem M sp t n nd mc mb mr ml) rom)
    /\ getr regs' 1 = (0x534ac : bv 64)%bv /\ getr regs' 10 = Z_to_bv 64 (ab + rz) /\ getr regs' 11 = Z_to_bv 64 190 /\ getr regs' 12 = Z_to_bv 64 4096
    /\ (forall r : reg, art_d2_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp ab n nd rz tp key tsd ctx t mc mb mr ml H2 H4 H9 H19 H20 Hsp Hsp' IMG Hn Hnd Hnd' Hub Hmc Hmb Hmr Hml
         W TSD Ht Ht' Timg A1 A2 A3 A4 A5 Cmc Cmb Cmr Cml Wts Ccf L Cmax Cfb.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  pose proof L as (G48 & Csb & G50 & Cmb0 & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
  unfold art_d2_large_mem.
  eexists. split; [|split; [|split; [|split; [|split]]]].
  - stepn F_532c8 D_532c8.
    zcall (art_thread_stats_fn _ _ _ _ sp tp key tsd ctx t).
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (Cmc' : cellA X (t + 2800) 8 mc) by (unfold apart in *; recell Cmc);
      assert (Cmb' : cellA X (t + 2800 + 8) 8 mb) by (unfold apart in *; recell Cmb);
      assert (Cmr' : cellA X (t + 2800 + 16) 8 mr) by (unfold apart in *; recell Cmr);
      assert (Wts' : wrA X (t + 2800) 112) by (repeat apply wr_Wn; exact Wts) end.
    zld F_532cc D_532cc (t + 2800 + 16) Cmr'.
    zld F_532d0 D_532d0 (t + 2800) Cmc'.
    zld F_532d4 D_532d4 (t + 2800 + 8) Cmb'.
    zstep F_532d8 D_532d8. zstep F_532dc D_532dc. zstep F_532e0 D_532e0. zstep F_532e4 D_532e4. zstep F_532e8 D_532e8. zstep F_532ec D_532ec.
    zsd F_532f0 D_532f0 (t + 2800) (mc + 1) ltac:(rewok Wts').
    zsd F_532f4 D_532f4 (t + 2800 + 8) (mb + n) ltac:(rewok Wts').
    zsd F_532f8 D_532f8 (t + 2800 + 16) (mr + (nd - n)) ltac:(rewok Wts').
    zbft F_532fc D_532fc.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cml' : cellA X (t + 2800 + 104) 8 ml) by (unfold apart in *; recell Cml) end.
    zld F_53300 D_53300 (t + 2800 + 104) Cml'.
    zstep F_53304 D_53304.
    zsd F_53308 D_53308 (t + 2800 + 104) (ml + 1) ltac:(rewok Wts').
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (Ccf' : cellA X (sp + 8) 8 1) by (unfold apart in *; recell Ccf);
      assert (G40' : cellA X 0x1391b0 8 0x13f1f8) by (unfold apart in *; recell G40);
      assert (Cmax' : cellA X (0x13f1f8 + 44) 4 4096) by (unfold apart in *; recell Cmax);
      assert (G68' : cellA X 0x1391d8 8 0x13b1c8) by (unfold apart in *; recell G68);
      assert (Crm' : cellA X 0x13b1c8 8 0x12b88c) by (unfold apart in *; recell Crm);
      assert (Cfb' : cellA X (0x13f1f8 + 52) 4 190) by (unfold apart in *; recell Cfb) end.
    zld F_5330c D_5330c (sp + 8) Ccf'.
    zbtk F_53310 D_53310.
    zstep F_53428 D_53428. zld F_5342c D_5342c 0x1391b0 G40'.
    zlw F_53430 D_53430 (0x13f1f8 + 44) Cmax'.
    zbft F_53434 D_53434.
    zstep F_53438 D_53438.
    zbft F_5343c D_5343c.
    zstep F_53440 D_53440.
    zstep F_53444 D_53444. zld F_53448 D_53448 0x1391d8 G68'. zld F_5344c D_5344c 0x13b1c8 Crm'.
    zlw F_53450 D_53450 (0x13f1f8 + 52) Cfb'.
    zstep F_53454 D_53454.
    stepjr F_53458 D_53458 (0x12b88c : bv 64)%bv ltac:(gres; bveq).
    apply mst_refl.
  - gres. apply bv_eq. reflexivity.
  - kept_solve.
  - kept_solve.
  - kept_solve.
  - intros r Hr. unfold art_d2_kept in Hr. decompose [and] Hr. kept_solve.
Qed.
End FPX.
