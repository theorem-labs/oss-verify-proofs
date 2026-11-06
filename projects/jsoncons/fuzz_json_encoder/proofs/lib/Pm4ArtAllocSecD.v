(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac Pm4ArtLeaf Pm4ArtPoison Pm4ArtAllocC Pm4ArtAllocD Pm4ArtAllocV.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import Pm4_code_5a000_5b000.
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
  art_layout M -> cellA M (0x1676f8 + 85) 1 1 -> (n mod 8 <> 0 -> wrA M (art_d1_addr ab rz n) 1) ->
  exists regs',
    msteps ASEGS (mkst regs (0x5ace0 : word) M rom) (mkst regs' (0x5ad74 : word) (art_d1_mem M ab rz n) rom)
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
      * zbft F_5ac90 D_5ac90.
        stepn F_5ac94 D_5ac94.
        zcall (art_can_poison_fn _ _ _ _).
        zbft F_5ac98 D_5ac98.
        zstep F_5ac9c D_5ac9c. zld F_5aca0 D_5aca0 0x160c18 G48. zld F_5aca4 D_5aca4 0x169ef8 Csb. unfold SB.
        zstep F_5aca8 D_5aca8. zstep F_5acac D_5acac. zstep F_5acb0 D_5acb0. zstep F_5acb4 D_5acb4. zstep F_5acb8 D_5acb8.
        zbtk F_5acbc D_5acbc.
        zstep F_5ad00 D_5ad00. zld F_5ad04 D_5ad04 0x160c10 G40.
        zlbu F_5ad08 D_5ad08 (0x1676f8 + 85) Cpp.
        stepn F_5ad0c D_5ad0c. rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
        zstep F_5ad10 D_5ad10. zstep F_5ad14 D_5ad14.
        stepn F_5ad18 D_5ad18. rwH. rewrite art_zb_and by lia. rewrite art_land_full_r by lia.
        stepn F_5ad1c D_5ad1c. rwH. rewrite art_zb_andi by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
        zsb F_5ad20 D_5ad20 (2147450880 + (ab + rz + n / 8 * 8) / 8) (n mod 8) ltac:(rewok Wsh).
        apply mst_refl.
      * intros r Hr. unfold art_d1_kept in Hr. decompose [and] Hr. kept_solve.
    + eexists. split.
      * zbft F_5ac90 D_5ac90.
        stepn F_5ac94 D_5ac94.
        zcall (art_can_poison_fn _ _ _ _).
        zbft F_5ac98 D_5ac98.
        zstep F_5ac9c D_5ac9c. zld F_5aca0 D_5aca0 0x160c18 G48. zld F_5aca4 D_5aca4 0x169ef8 Csb. unfold SB.
        zstep F_5aca8 D_5aca8. zstep F_5acac D_5acac. zstep F_5acb0 D_5acb0. zstep F_5acb4 D_5acb4. zstep F_5acb8 D_5acb8.
        zbft F_5acbc D_5acbc.
        zstep F_5acc0 D_5acc0. zld F_5acc4 D_5acc4 0x160c20 G50. zstep F_5acc8 D_5acc8. zld F_5accc D_5accc 0x160c28 G58.
        zld F_5acd0 D_5acd0 0x16abe8 Cmb. zld F_5acd4 D_5acd4 0x16abf0 Cme.
        zstep F_5acd8 D_5acd8.
        zbtk F_5acdc D_5acdc.
        zstep F_5ace4 D_5ace4. zld F_5ace8 D_5ace8 0x160c30 G60. zld F_5acec D_5acec 0x16abe0 Che. unfold kHighMemEnd.
        zstep F_5acf0 D_5acf0. zstep F_5acf4 D_5acf4.
        zbft F_5acf8 D_5acf8. zbft F_5acfc D_5acfc.
        zstep F_5ad00 D_5ad00. zld F_5ad04 D_5ad04 0x160c10 G40.
        zlbu F_5ad08 D_5ad08 (0x1676f8 + 85) Cpp.
        stepn F_5ad0c D_5ad0c. rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
        zstep F_5ad10 D_5ad10. zstep F_5ad14 D_5ad14.
        stepn F_5ad18 D_5ad18. rwH. rewrite art_zb_and by lia. rewrite art_land_full_r by lia.
        stepn F_5ad1c D_5ad1c. rwH. rewrite art_zb_andi by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
        zsb F_5ad20 D_5ad20 (2147450880 + (ab + rz + n / 8 * 8) / 8) (n mod 8) ltac:(rewok Wsh).
        apply mst_refl.
      * intros r Hr. unfold art_d1_kept in Hr. decompose [and] Hr. kept_solve.
Qed.

Definition art_d2_large_mem (M : word -> option byte) (sp t n nd mc mb mr ml : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) 0x5ad78) (sp - 24) 0x8b068) (t + 2800) (mc + 1)) (t + 2800 + 8) (mb + n)) (t + 2800 + 16) (mr + (nd - n)))
       (t + 2800 + 104) (ml + 1).

Definition art_d2_kept (r : reg) : Prop :=
  r <> 1%bv /\ r <> 10%bv /\ r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv.

Lemma art_alloc_d2_large_fn : forall regs (M rom : word -> option byte) (sp ab n nd rz tp key tsd ctx t mc mb mr ml : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> getr regs 9 = Z_to_bv 64 n -> getr regs 19 = Z_to_bv 64 nd -> getr regs 20 = Z_to_bv 64 (ab + rz) ->
  32 <= sp -> sp + 128 < 2 ^ 64 -> 0x6c0000 + 32 <= sp -> 4096 <= n -> n <= nd -> 65536 < nd < 2 ^ 40 -> 0 <= ab + rz < 2 ^ 64 ->
  0 <= mc < 2 ^ 64 -> 0 <= mb < 2 ^ 64 -> 0 <= mr < 2 ^ 64 -> 0 <= ml < 2 ^ 64 ->
  wrA M (sp - 32) 32 -> art_tsd M tp key tsd ctx t -> 4096 <= t -> t + 4096 < 2 ^ 64 -> (t + 4096 <= 0x10000 \/ 0x6c0000 <= t) ->
  apart (sp - 32) 32 0x169760 8 -> apart (sp - 32) 32 (tp - 88) 8 -> apart (sp - 32) 32 (tsd + 8 * key) 8 -> apart (sp - 32) 32 (ctx + 152) 8 ->
  apart (sp - 32) 160 (t + 2800) 112 ->
  cellA M (t + 2800) 8 mc -> cellA M (t + 2800 + 8) 8 mb -> cellA M (t + 2800 + 16) 8 mr -> cellA M (t + 2800 + 104) 8 ml -> wrA M (t + 2800) 112 ->
  cellA M (sp + 8) 8 1 -> art_layout M -> cellA M (0x1676f8 + 44) 4 4096 -> cellA M (0x1676f8 + 52) 4 190 ->
  exists regs',
    msteps ASEGS (mkst regs (0x5ad74 : word) M rom) (mkst regs' (0x152ea4 : word) (art_d2_large_mem M sp t n nd mc mb mr ml) rom)
    /\ getr regs' 1 = (0x5af08 : bv 64)%bv /\ getr regs' 10 = Z_to_bv 64 (ab + rz) /\ getr regs' 11 = Z_to_bv 64 190 /\ getr regs' 12 = Z_to_bv 64 4096
    /\ (forall r : reg, art_d2_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp ab n nd rz tp key tsd ctx t mc mb mr ml H2 H4 H9 H19 H20 Hsp Hsp' IMG Hn Hnd Hnd' Hub Hmc Hmb Hmr Hml
         W TSD Ht Ht' Timg A1 A2 A3 A4 A5 Cmc Cmb Cmr Cml Wts Ccf L Cmax Cfb.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  pose proof L as (G48 & Csb & G50 & Cmb0 & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
  unfold art_d2_large_mem.
  eexists. split; [|split; [|split; [|split; [|split]]]].
  - stepn F_5ad24 D_5ad24.
    zcall (art_thread_stats_fn _ _ _ _ sp tp key tsd ctx t).
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (Cmc' : cellA X (t + 2800) 8 mc) by (unfold apart in *; recell Cmc);
      assert (Cmb' : cellA X (t + 2800 + 8) 8 mb) by (unfold apart in *; recell Cmb);
      assert (Cmr' : cellA X (t + 2800 + 16) 8 mr) by (unfold apart in *; recell Cmr);
      assert (Wts' : wrA X (t + 2800) 112) by (repeat apply wr_Wn; exact Wts) end.
    zld F_5ad28 D_5ad28 (t + 2800 + 16) Cmr'.
    zld F_5ad2c D_5ad2c (t + 2800) Cmc'.
    zld F_5ad30 D_5ad30 (t + 2800 + 8) Cmb'.
    zstep F_5ad34 D_5ad34. zstep F_5ad38 D_5ad38. zstep F_5ad3c D_5ad3c. zstep F_5ad40 D_5ad40. zstep F_5ad44 D_5ad44. zstep F_5ad48 D_5ad48.
    zsd F_5ad4c D_5ad4c (t + 2800) (mc + 1) ltac:(rewok Wts').
    zsd F_5ad50 D_5ad50 (t + 2800 + 8) (mb + n) ltac:(rewok Wts').
    zsd F_5ad54 D_5ad54 (t + 2800 + 16) (mr + (nd - n)) ltac:(rewok Wts').
    zbft F_5ad58 D_5ad58.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cml' : cellA X (t + 2800 + 104) 8 ml) by (unfold apart in *; recell Cml) end.
    zld F_5ad5c D_5ad5c (t + 2800 + 104) Cml'.
    zstep F_5ad60 D_5ad60.
    zsd F_5ad64 D_5ad64 (t + 2800 + 104) (ml + 1) ltac:(rewok Wts').
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (Ccf' : cellA X (sp + 8) 8 1) by (unfold apart in *; recell Ccf);
      assert (G40' : cellA X 0x160c10 8 0x1676f8) by (unfold apart in *; recell G40);
      assert (Cmax' : cellA X (0x1676f8 + 44) 4 4096) by (unfold apart in *; recell Cmax);
      assert (G68' : cellA X 0x160c38 8 0x162c50) by (unfold apart in *; recell G68);
      assert (Crm' : cellA X 0x162c50 8 0x152ea4) by (unfold apart in *; recell Crm);
      assert (Cfb' : cellA X (0x1676f8 + 52) 4 190) by (unfold apart in *; recell Cfb) end.
    zld F_5ad68 D_5ad68 (sp + 8) Ccf'.
    zbtk F_5ad6c D_5ad6c.
    zstep F_5ae84 D_5ae84. zld F_5ae88 D_5ae88 0x160c10 G40'.
    zlw F_5ae8c D_5ae8c (0x1676f8 + 44) Cmax'.
    zbft F_5ae90 D_5ae90.
    zstep F_5ae94 D_5ae94.
    zbft F_5ae98 D_5ae98.
    zstep F_5ae9c D_5ae9c.
    zstep F_5aea0 D_5aea0. zld F_5aea4 D_5aea4 0x160c38 G68'. zld F_5aea8 D_5aea8 0x162c50 Crm'.
    zlw F_5aeac D_5aeac (0x1676f8 + 52) Cfb'.
    zstep F_5aeb0 D_5aeb0.
    stepjr F_5aeb4 D_5aeb4 (0x152ea4 : bv 64)%bv ltac:(gres; bveq).
    apply mst_refl.
  - gres. apply bv_eq. reflexivity.
  - kept_solve.
  - kept_solve.
  - kept_solve.
  - intros r Hr. unfold art_d2_kept in Hr. decompose [and] Hr. kept_solve.
Qed.
End FPX.
