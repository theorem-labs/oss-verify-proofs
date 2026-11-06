(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac BrtLeaf BrtPoison BrtAllocC BrtAllocD BrtAllocV.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import Bo0_code_3d2b4_3e23c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section FPX. Context {fx : PropExec.FPState}.

Lemma art_alloc_d1_any : forall regs (M rom : word -> option byte) (ab n rz : Z),
  getr regs 9 = Z_to_bv 64 n -> getr regs 20 = Z_to_bv 64 (ab + rz) -> getr regs 22 = Z_to_bv 64 (n / 8 * 8) ->
  4096 <= ab -> ab + rz + n < 2 ^ 47 -> (ab + rz + n < SB \/ kHighMemBeg <= ab) -> 16 <= rz <= 2048 -> 8 <= n < 2 ^ 40 ->
  art_layout M -> cellA M (0xdbf38 + 85) 1 1 -> (n mod 8 <> 0 -> wrA M (art_d1_addr ab rz n) 1) ->
  exists regs',
    msteps ASEGS (mkst regs (0x3daa8 : word) M rom) (mkst regs' (0x3db3c : word) (art_d1_mem M ab rz n) rom)
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
      * zbft F_3daa8 D_3daa8.
        stepn F_3daac D_3daac.
        zcall (art_can_poison_fn _ _ _ _).
        zbft F_3dab0 D_3dab0.
        zstep F_3dab4 D_3dab4. zld F_3dab8 D_3dab8 0xd64c8 G48. zld F_3dabc D_3dabc 0xde738 Csb. unfold SB.
        zstep F_3dac0 D_3dac0. zstep F_3dac4 D_3dac4. zstep F_3dac8 D_3dac8. zstep F_3dacc D_3dacc. zstep F_3dad0 D_3dad0.
        zbtk F_3dad4 D_3dad4.
        zstep F_3db18 D_3db18. zld F_3db1c D_3db1c 0xd64c0 G40.
        zlbu F_3db20 D_3db20 (0xdbf38 + 85) Cpp.
        stepn F_3db24 D_3db24. rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
        zstep F_3db28 D_3db28. zstep F_3db2c D_3db2c.
        stepn F_3db30 D_3db30. rwH. rewrite art_zb_and by lia. rewrite art_land_full_r by lia.
        stepn F_3db34 D_3db34. rwH. rewrite art_zb_andi by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
        zsb F_3db38 D_3db38 (2147450880 + (ab + rz + n / 8 * 8) / 8) (n mod 8) ltac:(rewok Wsh).
        apply mst_refl.
      * intros r Hr. unfold art_d1_kept in Hr. decompose [and] Hr. kept_solve.
    + eexists. split.
      * zbft F_3daa8 D_3daa8.
        stepn F_3daac D_3daac.
        zcall (art_can_poison_fn _ _ _ _).
        zbft F_3dab0 D_3dab0.
        zstep F_3dab4 D_3dab4. zld F_3dab8 D_3dab8 0xd64c8 G48. zld F_3dabc D_3dabc 0xde738 Csb. unfold SB.
        zstep F_3dac0 D_3dac0. zstep F_3dac4 D_3dac4. zstep F_3dac8 D_3dac8. zstep F_3dacc D_3dacc. zstep F_3dad0 D_3dad0.
        zbft F_3dad4 D_3dad4.
        zstep F_3dad8 D_3dad8. zld F_3dadc D_3dadc 0xd64d0 G50. zstep F_3dae0 D_3dae0. zld F_3dae4 D_3dae4 0xd64d8 G58.
        zld F_3dae8 D_3dae8 0xdf428 Cmb. zld F_3daec D_3daec 0xdf430 Cme.
        zstep F_3daf0 D_3daf0.
        zbtk F_3daf4 D_3daf4.
        zstep F_3dafc D_3dafc. zld F_3db00 D_3db00 0xd64e0 G60. zld F_3db04 D_3db04 0xdf420 Che. unfold kHighMemEnd.
        zstep F_3db08 D_3db08. zstep F_3db0c D_3db0c.
        zbft F_3db10 D_3db10. zbft F_3db14 D_3db14.
        zstep F_3db18 D_3db18. zld F_3db1c D_3db1c 0xd64c0 G40.
        zlbu F_3db20 D_3db20 (0xdbf38 + 85) Cpp.
        stepn F_3db24 D_3db24. rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
        zstep F_3db28 D_3db28. zstep F_3db2c D_3db2c.
        stepn F_3db30 D_3db30. rwH. rewrite art_zb_and by lia. rewrite art_land_full_r by lia.
        stepn F_3db34 D_3db34. rwH. rewrite art_zb_andi by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
        zsb F_3db38 D_3db38 (2147450880 + (ab + rz + n / 8 * 8) / 8) (n mod 8) ltac:(rewok Wsh).
        apply mst_refl.
      * intros r Hr. unfold art_d1_kept in Hr. decompose [and] Hr. kept_solve.
Qed.

Definition art_d2_large_mem (M : word -> option byte) (sp t n nd mc mb mr ml : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) 0x3db40) (sp - 24) 0x68c3c) (t + 2800) (mc + 1)) (t + 2800 + 8) (mb + n)) (t + 2800 + 16) (mr + (nd - n)))
       (t + 2800 + 104) (ml + 1).

Definition art_d2_kept (r : reg) : Prop :=
  r <> 1%bv /\ r <> 10%bv /\ r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv.

Lemma art_alloc_d2_large_fn : forall regs (M rom : word -> option byte) (sp ab n nd rz tp key tsd ctx t mc mb mr ml : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> getr regs 9 = Z_to_bv 64 n -> getr regs 19 = Z_to_bv 64 nd -> getr regs 20 = Z_to_bv 64 (ab + rz) ->
  32 <= sp -> sp + 128 < 2 ^ 64 -> 0x634000 + 32 <= sp -> 4096 <= n -> n <= nd -> 65536 < nd < 2 ^ 40 -> 0 <= ab + rz < 2 ^ 64 ->
  0 <= mc < 2 ^ 64 -> 0 <= mb < 2 ^ 64 -> 0 <= mr < 2 ^ 64 -> 0 <= ml < 2 ^ 64 ->
  wrA M (sp - 32) 32 -> art_tsd M tp key tsd ctx t -> 4096 <= t -> t + 4096 < 2 ^ 64 -> (t + 4096 <= 0x10000 \/ 0x634000 <= t) ->
  apart (sp - 32) 32 0xddfa0 8 -> apart (sp - 32) 32 (tp - 88) 8 -> apart (sp - 32) 32 (tsd + 8 * key) 8 -> apart (sp - 32) 32 (ctx + 152) 8 ->
  apart (sp - 32) 160 (t + 2800) 112 ->
  cellA M (t + 2800) 8 mc -> cellA M (t + 2800 + 8) 8 mb -> cellA M (t + 2800 + 16) 8 mr -> cellA M (t + 2800 + 104) 8 ml -> wrA M (t + 2800) 112 ->
  cellA M (sp + 8) 8 1 -> art_layout M -> cellA M (0xdbf38 + 44) 4 4096 -> cellA M (0xdbf38 + 52) 4 190 ->
  exists regs',
    msteps ASEGS (mkst regs (0x3db3c : word) M rom) (mkst regs' (0xcc740 : word) (art_d2_large_mem M sp t n nd mc mb mr ml) rom)
    /\ getr regs' 1 = (0x3dcd0 : bv 64)%bv /\ getr regs' 10 = Z_to_bv 64 (ab + rz) /\ getr regs' 11 = Z_to_bv 64 190 /\ getr regs' 12 = Z_to_bv 64 4096
    /\ (forall r : reg, art_d2_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp ab n nd rz tp key tsd ctx t mc mb mr ml H2 H4 H9 H19 H20 Hsp Hsp' IMG Hn Hnd Hnd' Hub Hmc Hmb Hmr Hml
         W TSD Ht Ht' Timg A1 A2 A3 A4 A5 Cmc Cmb Cmr Cml Wts Ccf L Cmax Cfb.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  pose proof L as (G48 & Csb & G50 & Cmb0 & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
  unfold art_d2_large_mem.
  eexists. split; [|split; [|split; [|split; [|split]]]].
  - stepn F_3db3c D_3db3c.
    zcall (art_thread_stats_fn _ _ _ _ sp tp key tsd ctx t).
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (Cmc' : cellA X (t + 2800) 8 mc) by (unfold apart in *; recell Cmc);
      assert (Cmb' : cellA X (t + 2800 + 8) 8 mb) by (unfold apart in *; recell Cmb);
      assert (Cmr' : cellA X (t + 2800 + 16) 8 mr) by (unfold apart in *; recell Cmr);
      assert (Wts' : wrA X (t + 2800) 112) by (repeat apply wr_Wn; exact Wts) end.
    zld F_3db40 D_3db40 (t + 2800 + 16) Cmr'.
    zld F_3db44 D_3db44 (t + 2800) Cmc'.
    zld F_3db48 D_3db48 (t + 2800 + 8) Cmb'.
    zstep F_3db4c D_3db4c. zstep F_3db50 D_3db50. zstep F_3db54 D_3db54. zstep F_3db58 D_3db58. zstep F_3db5c D_3db5c. zstep F_3db60 D_3db60.
    zsd F_3db64 D_3db64 (t + 2800) (mc + 1) ltac:(rewok Wts').
    zsd F_3db68 D_3db68 (t + 2800 + 8) (mb + n) ltac:(rewok Wts').
    zsd F_3db6c D_3db6c (t + 2800 + 16) (mr + (nd - n)) ltac:(rewok Wts').
    zbft F_3db70 D_3db70.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cml' : cellA X (t + 2800 + 104) 8 ml) by (unfold apart in *; recell Cml) end.
    zld F_3db74 D_3db74 (t + 2800 + 104) Cml'.
    zstep F_3db78 D_3db78.
    zsd F_3db7c D_3db7c (t + 2800 + 104) (ml + 1) ltac:(rewok Wts').
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (Ccf' : cellA X (sp + 8) 8 1) by (unfold apart in *; recell Ccf);
      assert (G40' : cellA X 0xd64c0 8 0xdbf38) by (unfold apart in *; recell G40);
      assert (Cmax' : cellA X (0xdbf38 + 44) 4 4096) by (unfold apart in *; recell Cmax);
      assert (G68' : cellA X 0xd64e8 8 0xd8428) by (unfold apart in *; recell G68);
      assert (Crm' : cellA X 0xd8428 8 0xcc740) by (unfold apart in *; recell Crm);
      assert (Cfb' : cellA X (0xdbf38 + 52) 4 190) by (unfold apart in *; recell Cfb) end.
    zld F_3db80 D_3db80 (sp + 8) Ccf'.
    zbtk F_3db84 D_3db84.
    zstep F_3dc9c D_3dc9c. zld F_3dca0 D_3dca0 0xd64c0 G40'.
    zlw F_3dca4 D_3dca4 (0xdbf38 + 44) Cmax'.
    zbft F_3dca8 D_3dca8.
    zstep F_3dcac D_3dcac.
    zbft F_3dcb0 D_3dcb0.
    zstep F_3dcb4 D_3dcb4.
    zstep F_3dcb8 D_3dcb8. zld F_3dcbc D_3dcbc 0xd64e8 G68'. zld F_3dcc0 D_3dcc0 0xd8428 Crm'.
    zlw F_3dcc4 D_3dcc4 (0xdbf38 + 52) Cfb'.
    zstep F_3dcc8 D_3dcc8.
    stepjr F_3dccc D_3dccc (0xcc740 : bv 64)%bv ltac:(gres; bveq).
    apply mst_refl.
  - gres. apply bv_eq. reflexivity.
  - kept_solve.
  - kept_solve.
  - kept_solve.
  - intros r Hr. unfold art_d2_kept in Hr. decompose [and] Hr. kept_solve.
Qed.
End FPX.
