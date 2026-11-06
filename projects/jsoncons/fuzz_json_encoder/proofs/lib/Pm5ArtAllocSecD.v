(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac Pm5ArtLeaf Pm5ArtPoison Pm5ArtAllocC Pm5ArtAllocD Pm5ArtAllocV.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import Pm5_code_5b000_5c000.
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
  art_layout M -> cellA M (0x16afb8 + 85) 1 1 -> (n mod 8 <> 0 -> wrA M (art_d1_addr ab rz n) 1) ->
  exists regs',
    msteps ASEGS (mkst regs (0x5b5b0 : word) M rom) (mkst regs' (0x5b644 : word) (art_d1_mem M ab rz n) rom)
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
      * zbft F_5b568 D_5b568.
        stepn F_5b56c D_5b56c.
        zcall (art_can_poison_fn _ _ _ _).
        zbft F_5b570 D_5b570.
        zstep F_5b574 D_5b574. zld F_5b578 D_5b578 0x164518 G48. zld F_5b57c D_5b57c 0x16d7b8 Csb. unfold SB.
        zstep F_5b580 D_5b580. zstep F_5b584 D_5b584. zstep F_5b588 D_5b588. zstep F_5b58c D_5b58c. zstep F_5b590 D_5b590.
        zbtk F_5b594 D_5b594.
        zstep F_5b5d8 D_5b5d8. zld F_5b5dc D_5b5dc 0x164510 G40.
        zlbu F_5b5e0 D_5b5e0 (0x16afb8 + 85) Cpp.
        stepn F_5b5e4 D_5b5e4. rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
        zstep F_5b5e8 D_5b5e8. zstep F_5b5ec D_5b5ec.
        stepn F_5b5f0 D_5b5f0. rwH. rewrite art_zb_and by lia. rewrite art_land_full_r by lia.
        stepn F_5b5f4 D_5b5f4. rwH. rewrite art_zb_andi by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
        zsb F_5b5f8 D_5b5f8 (2147450880 + (ab + rz + n / 8 * 8) / 8) (n mod 8) ltac:(rewok Wsh).
        apply mst_refl.
      * intros r Hr. unfold art_d1_kept in Hr. decompose [and] Hr. kept_solve.
    + eexists. split.
      * zbft F_5b568 D_5b568.
        stepn F_5b56c D_5b56c.
        zcall (art_can_poison_fn _ _ _ _).
        zbft F_5b570 D_5b570.
        zstep F_5b574 D_5b574. zld F_5b578 D_5b578 0x164518 G48. zld F_5b57c D_5b57c 0x16d7b8 Csb. unfold SB.
        zstep F_5b580 D_5b580. zstep F_5b584 D_5b584. zstep F_5b588 D_5b588. zstep F_5b58c D_5b58c. zstep F_5b590 D_5b590.
        zbft F_5b594 D_5b594.
        zstep F_5b598 D_5b598. zld F_5b59c D_5b59c 0x164520 G50. zstep F_5b5a0 D_5b5a0. zld F_5b5a4 D_5b5a4 0x164528 G58.
        zld F_5b5a8 D_5b5a8 0x16e4a8 Cmb. zld F_5b5ac D_5b5ac 0x16e4b0 Cme.
        zstep F_5b5b0 D_5b5b0.
        zbtk F_5b5b4 D_5b5b4.
        zstep F_5b5bc D_5b5bc. zld F_5b5c0 D_5b5c0 0x164530 G60. zld F_5b5c4 D_5b5c4 0x16e4a0 Che. unfold kHighMemEnd.
        zstep F_5b5c8 D_5b5c8. zstep F_5b5cc D_5b5cc.
        zbft F_5b5d0 D_5b5d0. zbft F_5b5d4 D_5b5d4.
        zstep F_5b5d8 D_5b5d8. zld F_5b5dc D_5b5dc 0x164510 G40.
        zlbu F_5b5e0 D_5b5e0 (0x16afb8 + 85) Cpp.
        stepn F_5b5e4 D_5b5e4. rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
        zstep F_5b5e8 D_5b5e8. zstep F_5b5ec D_5b5ec.
        stepn F_5b5f0 D_5b5f0. rwH. rewrite art_zb_and by lia. rewrite art_land_full_r by lia.
        stepn F_5b5f4 D_5b5f4. rwH. rewrite art_zb_andi by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
        zsb F_5b5f8 D_5b5f8 (2147450880 + (ab + rz + n / 8 * 8) / 8) (n mod 8) ltac:(rewok Wsh).
        apply mst_refl.
      * intros r Hr. unfold art_d1_kept in Hr. decompose [and] Hr. kept_solve.
Qed.

Definition art_d2_large_mem (M : word -> option byte) (sp t n nd mc mb mr ml : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) 0x5b648) (sp - 24) 0x8b938) (t + 2800) (mc + 1)) (t + 2800 + 8) (mb + n)) (t + 2800 + 16) (mr + (nd - n)))
       (t + 2800 + 104) (ml + 1).

Definition art_d2_kept (r : reg) : Prop :=
  r <> 1%bv /\ r <> 10%bv /\ r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv.

Lemma art_alloc_d2_large_fn : forall regs (M rom : word -> option byte) (sp ab n nd rz tp key tsd ctx t mc mb mr ml : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> getr regs 9 = Z_to_bv 64 n -> getr regs 19 = Z_to_bv 64 nd -> getr regs 20 = Z_to_bv 64 (ab + rz) ->
  32 <= sp -> sp + 128 < 2 ^ 64 -> 0x6c4000 + 32 <= sp -> 4096 <= n -> n <= nd -> 65536 < nd < 2 ^ 40 -> 0 <= ab + rz < 2 ^ 64 ->
  0 <= mc < 2 ^ 64 -> 0 <= mb < 2 ^ 64 -> 0 <= mr < 2 ^ 64 -> 0 <= ml < 2 ^ 64 ->
  wrA M (sp - 32) 32 -> art_tsd M tp key tsd ctx t -> 4096 <= t -> t + 4096 < 2 ^ 64 -> (t + 4096 <= 0x10000 \/ 0x6c4000 <= t) ->
  apart (sp - 32) 32 0x16d020 8 -> apart (sp - 32) 32 (tp - 88) 8 -> apart (sp - 32) 32 (tsd + 8 * key) 8 -> apart (sp - 32) 32 (ctx + 152) 8 ->
  apart (sp - 32) 160 (t + 2800) 112 ->
  cellA M (t + 2800) 8 mc -> cellA M (t + 2800 + 8) 8 mb -> cellA M (t + 2800 + 16) 8 mr -> cellA M (t + 2800 + 104) 8 ml -> wrA M (t + 2800) 112 ->
  cellA M (sp + 8) 8 1 -> art_layout M -> cellA M (0x16afb8 + 44) 4 4096 -> cellA M (0x16afb8 + 52) 4 190 ->
  exists regs',
    msteps ASEGS (mkst regs (0x5b644 : word) M rom) (mkst regs' (0x1568bc : word) (art_d2_large_mem M sp t n nd mc mb mr ml) rom)
    /\ getr regs' 1 = (0x5b7d8 : bv 64)%bv /\ getr regs' 10 = Z_to_bv 64 (ab + rz) /\ getr regs' 11 = Z_to_bv 64 190 /\ getr regs' 12 = Z_to_bv 64 4096
    /\ (forall r : reg, art_d2_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp ab n nd rz tp key tsd ctx t mc mb mr ml H2 H4 H9 H19 H20 Hsp Hsp' IMG Hn Hnd Hnd' Hub Hmc Hmb Hmr Hml
         W TSD Ht Ht' Timg A1 A2 A3 A4 A5 Cmc Cmb Cmr Cml Wts Ccf L Cmax Cfb.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  pose proof L as (G48 & Csb & G50 & Cmb0 & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
  unfold art_d2_large_mem.
  eexists. split; [|split; [|split; [|split; [|split]]]].
  - stepn F_5b5fc D_5b5fc.
    zcall (art_thread_stats_fn _ _ _ _ sp tp key tsd ctx t).
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (Cmc' : cellA X (t + 2800) 8 mc) by (unfold apart in *; recell Cmc);
      assert (Cmb' : cellA X (t + 2800 + 8) 8 mb) by (unfold apart in *; recell Cmb);
      assert (Cmr' : cellA X (t + 2800 + 16) 8 mr) by (unfold apart in *; recell Cmr);
      assert (Wts' : wrA X (t + 2800) 112) by (repeat apply wr_Wn; exact Wts) end.
    zld F_5b600 D_5b600 (t + 2800 + 16) Cmr'.
    zld F_5b604 D_5b604 (t + 2800) Cmc'.
    zld F_5b608 D_5b608 (t + 2800 + 8) Cmb'.
    zstep F_5b60c D_5b60c. zstep F_5b610 D_5b610. zstep F_5b614 D_5b614. zstep F_5b618 D_5b618. zstep F_5b61c D_5b61c. zstep F_5b620 D_5b620.
    zsd F_5b624 D_5b624 (t + 2800) (mc + 1) ltac:(rewok Wts').
    zsd F_5b628 D_5b628 (t + 2800 + 8) (mb + n) ltac:(rewok Wts').
    zsd F_5b62c D_5b62c (t + 2800 + 16) (mr + (nd - n)) ltac:(rewok Wts').
    zbft F_5b630 D_5b630.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cml' : cellA X (t + 2800 + 104) 8 ml) by (unfold apart in *; recell Cml) end.
    zld F_5b634 D_5b634 (t + 2800 + 104) Cml'.
    zstep F_5b638 D_5b638.
    zsd F_5b63c D_5b63c (t + 2800 + 104) (ml + 1) ltac:(rewok Wts').
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (Ccf' : cellA X (sp + 8) 8 1) by (unfold apart in *; recell Ccf);
      assert (G40' : cellA X 0x164510 8 0x16afb8) by (unfold apart in *; recell G40);
      assert (Cmax' : cellA X (0x16afb8 + 44) 4 4096) by (unfold apart in *; recell Cmax);
      assert (G68' : cellA X 0x164538 8 0x166550) by (unfold apart in *; recell G68);
      assert (Crm' : cellA X 0x166550 8 0x1568bc) by (unfold apart in *; recell Crm);
      assert (Cfb' : cellA X (0x16afb8 + 52) 4 190) by (unfold apart in *; recell Cfb) end.
    zld F_5b640 D_5b640 (sp + 8) Ccf'.
    zbtk F_5b644 D_5b644.
    zstep F_5b75c D_5b75c. zld F_5b760 D_5b760 0x164510 G40'.
    zlw F_5b764 D_5b764 (0x16afb8 + 44) Cmax'.
    zbft F_5b768 D_5b768.
    zstep F_5b76c D_5b76c.
    zbft F_5b770 D_5b770.
    zstep F_5b774 D_5b774.
    zstep F_5b778 D_5b778. zld F_5b77c D_5b77c 0x164538 G68'. zld F_5b780 D_5b780 0x166550 Crm'.
    zlw F_5b784 D_5b784 (0x16afb8 + 52) Cfb'.
    zstep F_5b788 D_5b788.
    stepjr F_5b78c D_5b78c (0x1568bc : bv 64)%bv ltac:(gres; bveq).
    apply mst_refl.
  - gres. apply bv_eq. reflexivity.
  - kept_solve.
  - kept_solve.
  - kept_solve.
  - intros r Hr. unfold art_d2_kept in Hr. decompose [and] Hr. kept_solve.
Qed.
End FPX.
