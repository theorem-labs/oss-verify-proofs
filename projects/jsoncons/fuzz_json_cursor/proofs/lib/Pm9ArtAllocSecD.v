(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac Pm9ArtLeaf Pm9ArtPoison Pm9ArtAllocC Pm9ArtAllocD Pm9ArtAllocV.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm9_code_59000_5a000.
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
  art_layout M -> cellA M (0x15b4f8 + 85) 1 1 -> (n mod 8 <> 0 -> wrA M (art_d1_addr ab rz n) 1) ->
  exists regs',
    msteps ASEGS (mkst regs (0x59cd4 : word) M rom) (mkst regs' (0x59d68 : word) (art_d1_mem M ab rz n) rom)
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
      * zbft F_59c8c D_59c8c.
        stepn F_59c90 D_59c90.
        zcall (art_can_poison_fn _ _ _ _).
        zbft F_59c94 D_59c94.
        zstep F_59c98 D_59c98. zld F_59c9c D_59c9c 0x154500 G48. zld F_59ca0 D_59ca0 0x15dcf8 Csb. unfold SB.
        zstep F_59ca4 D_59ca4. zstep F_59ca8 D_59ca8. zstep F_59cac D_59cac. zstep F_59cb0 D_59cb0. zstep F_59cb4 D_59cb4.
        zbtk F_59cb8 D_59cb8.
        zstep F_59cfc D_59cfc. zld F_59d00 D_59d00 0x1544f8 G40.
        zlbu F_59d04 D_59d04 (0x15b4f8 + 85) Cpp.
        stepn F_59d08 D_59d08. rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
        zstep F_59d0c D_59d0c. zstep F_59d10 D_59d10.
        stepn F_59d14 D_59d14. rwH. rewrite art_zb_and by lia. rewrite art_land_full_r by lia.
        stepn F_59d18 D_59d18. rwH. rewrite art_zb_andi by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
        zsb F_59d1c D_59d1c (2147450880 + (ab + rz + n / 8 * 8) / 8) (n mod 8) ltac:(rewok Wsh).
        apply mst_refl.
      * intros r Hr. unfold art_d1_kept in Hr. decompose [and] Hr. kept_solve.
    + eexists. split.
      * zbft F_59c8c D_59c8c.
        stepn F_59c90 D_59c90.
        zcall (art_can_poison_fn _ _ _ _).
        zbft F_59c94 D_59c94.
        zstep F_59c98 D_59c98. zld F_59c9c D_59c9c 0x154500 G48. zld F_59ca0 D_59ca0 0x15dcf8 Csb. unfold SB.
        zstep F_59ca4 D_59ca4. zstep F_59ca8 D_59ca8. zstep F_59cac D_59cac. zstep F_59cb0 D_59cb0. zstep F_59cb4 D_59cb4.
        zbft F_59cb8 D_59cb8.
        zstep F_59cbc D_59cbc. zld F_59cc0 D_59cc0 0x154508 G50. zstep F_59cc4 D_59cc4. zld F_59cc8 D_59cc8 0x154510 G58.
        zld F_59ccc D_59ccc 0x15e9e8 Cmb. zld F_59cd0 D_59cd0 0x15e9f0 Cme.
        zstep F_59cd4 D_59cd4.
        zbtk F_59cd8 D_59cd8.
        zstep F_59ce0 D_59ce0. zld F_59ce4 D_59ce4 0x154518 G60. zld F_59ce8 D_59ce8 0x15e9e0 Che. unfold kHighMemEnd.
        zstep F_59cec D_59cec. zstep F_59cf0 D_59cf0.
        zbft F_59cf4 D_59cf4. zbft F_59cf8 D_59cf8.
        zstep F_59cfc D_59cfc. zld F_59d00 D_59d00 0x1544f8 G40.
        zlbu F_59d04 D_59d04 (0x15b4f8 + 85) Cpp.
        stepn F_59d08 D_59d08. rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
        zstep F_59d0c D_59d0c. zstep F_59d10 D_59d10.
        stepn F_59d14 D_59d14. rwH. rewrite art_zb_and by lia. rewrite art_land_full_r by lia.
        stepn F_59d18 D_59d18. rwH. rewrite art_zb_andi by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
        zsb F_59d1c D_59d1c (2147450880 + (ab + rz + n / 8 * 8) / 8) (n mod 8) ltac:(rewok Wsh).
        apply mst_refl.
      * intros r Hr. unfold art_d1_kept in Hr. decompose [and] Hr. kept_solve.
Qed.

Definition art_d2_large_mem (M : word -> option byte) (sp t n nd mc mb mr ml : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) 0x59d6c) (sp - 24) 0x8a05c) (t + 2800) (mc + 1)) (t + 2800 + 8) (mb + n)) (t + 2800 + 16) (mr + (nd - n)))
       (t + 2800 + 104) (ml + 1).

Definition art_d2_kept (r : reg) : Prop :=
  r <> 1%bv /\ r <> 10%bv /\ r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv.

Lemma art_alloc_d2_large_fn : forall regs (M rom : word -> option byte) (sp ab n nd rz tp key tsd ctx t mc mb mr ml : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> getr regs 9 = Z_to_bv 64 n -> getr regs 19 = Z_to_bv 64 nd -> getr regs 20 = Z_to_bv 64 (ab + rz) ->
  32 <= sp -> sp + 128 < 2 ^ 64 -> 0x6b4000 + 32 <= sp -> 4096 <= n -> n <= nd -> 65536 < nd < 2 ^ 40 -> 0 <= ab + rz < 2 ^ 64 ->
  0 <= mc < 2 ^ 64 -> 0 <= mb < 2 ^ 64 -> 0 <= mr < 2 ^ 64 -> 0 <= ml < 2 ^ 64 ->
  wrA M (sp - 32) 32 -> art_tsd M tp key tsd ctx t -> 4096 <= t -> t + 4096 < 2 ^ 64 -> (t + 4096 <= 0x10000 \/ 0x6b4000 <= t) ->
  apart (sp - 32) 32 0x15d560 8 -> apart (sp - 32) 32 (tp - 88) 8 -> apart (sp - 32) 32 (tsd + 8 * key) 8 -> apart (sp - 32) 32 (ctx + 152) 8 ->
  apart (sp - 32) 160 (t + 2800) 112 ->
  cellA M (t + 2800) 8 mc -> cellA M (t + 2800 + 8) 8 mb -> cellA M (t + 2800 + 16) 8 mr -> cellA M (t + 2800 + 104) 8 ml -> wrA M (t + 2800) 112 ->
  cellA M (sp + 8) 8 1 -> art_layout M -> cellA M (0x15b4f8 + 44) 4 4096 -> cellA M (0x15b4f8 + 52) 4 190 ->
  exists regs',
    msteps ASEGS (mkst regs (0x59d68 : word) M rom) (mkst regs' (0x1468c4 : word) (art_d2_large_mem M sp t n nd mc mb mr ml) rom)
    /\ getr regs' 1 = (0x59efc : bv 64)%bv /\ getr regs' 10 = Z_to_bv 64 (ab + rz) /\ getr regs' 11 = Z_to_bv 64 190 /\ getr regs' 12 = Z_to_bv 64 4096
    /\ (forall r : reg, art_d2_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp ab n nd rz tp key tsd ctx t mc mb mr ml H2 H4 H9 H19 H20 Hsp Hsp' IMG Hn Hnd Hnd' Hub Hmc Hmb Hmr Hml
         W TSD Ht Ht' Timg A1 A2 A3 A4 A5 Cmc Cmb Cmr Cml Wts Ccf L Cmax Cfb.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  pose proof L as (G48 & Csb & G50 & Cmb0 & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
  unfold art_d2_large_mem.
  eexists. split; [|split; [|split; [|split; [|split]]]].
  - stepn F_59d20 D_59d20.
    zcall (art_thread_stats_fn _ _ _ _ sp tp key tsd ctx t).
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (Cmc' : cellA X (t + 2800) 8 mc) by (unfold apart in *; recell Cmc);
      assert (Cmb' : cellA X (t + 2800 + 8) 8 mb) by (unfold apart in *; recell Cmb);
      assert (Cmr' : cellA X (t + 2800 + 16) 8 mr) by (unfold apart in *; recell Cmr);
      assert (Wts' : wrA X (t + 2800) 112) by (repeat apply wr_Wn; exact Wts) end.
    zld F_59d24 D_59d24 (t + 2800 + 16) Cmr'.
    zld F_59d28 D_59d28 (t + 2800) Cmc'.
    zld F_59d2c D_59d2c (t + 2800 + 8) Cmb'.
    zstep F_59d30 D_59d30. zstep F_59d34 D_59d34. zstep F_59d38 D_59d38. zstep F_59d3c D_59d3c. zstep F_59d40 D_59d40. zstep F_59d44 D_59d44.
    zsd F_59d48 D_59d48 (t + 2800) (mc + 1) ltac:(rewok Wts').
    zsd F_59d4c D_59d4c (t + 2800 + 8) (mb + n) ltac:(rewok Wts').
    zsd F_59d50 D_59d50 (t + 2800 + 16) (mr + (nd - n)) ltac:(rewok Wts').
    zbft F_59d54 D_59d54.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cml' : cellA X (t + 2800 + 104) 8 ml) by (unfold apart in *; recell Cml) end.
    zld F_59d58 D_59d58 (t + 2800 + 104) Cml'.
    zstep F_59d5c D_59d5c.
    zsd F_59d60 D_59d60 (t + 2800 + 104) (ml + 1) ltac:(rewok Wts').
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (Ccf' : cellA X (sp + 8) 8 1) by (unfold apart in *; recell Ccf);
      assert (G40' : cellA X 0x1544f8 8 0x15b4f8) by (unfold apart in *; recell G40);
      assert (Cmax' : cellA X (0x15b4f8 + 44) 4 4096) by (unfold apart in *; recell Cmax);
      assert (G68' : cellA X 0x154520 8 0x156528) by (unfold apart in *; recell G68);
      assert (Crm' : cellA X 0x156528 8 0x1468c4) by (unfold apart in *; recell Crm);
      assert (Cfb' : cellA X (0x15b4f8 + 52) 4 190) by (unfold apart in *; recell Cfb) end.
    zld F_59d64 D_59d64 (sp + 8) Ccf'.
    zbtk F_59d68 D_59d68.
    zstep F_59e80 D_59e80. zld F_59e84 D_59e84 0x1544f8 G40'.
    zlw F_59e88 D_59e88 (0x15b4f8 + 44) Cmax'.
    zbft F_59e8c D_59e8c.
    zstep F_59e90 D_59e90.
    zbft F_59e94 D_59e94.
    zstep F_59e98 D_59e98.
    zstep F_59e9c D_59e9c. zld F_59ea0 D_59ea0 0x154520 G68'. zld F_59ea4 D_59ea4 0x156528 Crm'.
    zlw F_59ea8 D_59ea8 (0x15b4f8 + 52) Cfb'.
    zstep F_59eac D_59eac.
    stepjr F_59eb0 D_59eb0 (0x1468c4 : bv 64)%bv ltac:(gres; bveq).
    apply mst_refl.
  - gres. apply bv_eq. reflexivity.
  - kept_solve.
  - kept_solve.
  - kept_solve.
  - intros r Hr. unfold art_d2_kept in Hr. decompose [and] Hr. kept_solve.
Qed.
End FPX.
