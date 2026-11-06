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
     ArtMem ArtRegs ArtAtomics ArtTac Pm5ArtLeaf Pm5ArtPoison Pm5ArtSecAlloc Pm5ArtAllocC.
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

(* [comment removed for export] *)
Lemma art_alloc_csec_range : forall regs (M rom : word -> option byte) (ia ab spb : Z),
  getr regs 18 = Z_to_bv 64 ab -> getr regs 22 = Z_to_bv 64 ia ->
  0 <= ia -> ia + 4096 < 2 ^ 64 -> 0 <= ab < 2 ^ 48 -> 0 <= spb -> spb + 2 ^ 37 < 2 ^ 48 -> (ab < spb \/ spb + 2 ^ 37 <= ab) ->
  cellA M (ia + 32) 8 spb ->
  exists regs',
    msteps ASEGS (mkst regs (0x5b4d4 : word) M rom) (mkst regs' (0x5b510 : word) M rom)
    /\ (forall x : reg, x <> 10%bv -> x <> 11%bv -> getr regs' x = getr regs x).
Proof.
  intros regs M rom ia ab spb H18 H22 Hia Hia' Hab Hspb Hspb' OUT Cspb.
  destruct OUT as [LO|HI].
  - eexists. split.
    + zld F_5b48c D_5b48c (ia + 32) Cspb. zbtk F_5b490 D_5b490. apply mst_refl.
    + intros; kept_solve.
  - eexists. split.
    + zld F_5b48c D_5b48c (ia + 32) Cspb. zbft F_5b490 D_5b490.
      zstep F_5b494 D_5b494. zstep F_5b498 D_5b498. zstep F_5b49c D_5b49c.
      zbtk F_5b4a0 D_5b4a0. apply mst_refl.
    + intros; kept_solve.
Qed.

Lemma art_alloc_csec1 : forall regs (M rom : word -> option byte) (ia ab n rz id nd q spb : Z),
  getr regs 10 = Z_to_bv 64 id -> getr regs 8 = Z_to_bv 64 0 -> getr regs 9 = Z_to_bv 64 n -> getr regs 18 = Z_to_bv 64 ab ->
  getr regs 20 = Z_to_bv 64 (ab + rz) -> getr regs 21 = Z_to_bv 64 (ab + rz - 16) -> getr regs 22 = Z_to_bv 64 ia -> getr regs 24 = Z_to_bv 64 0 ->
  getr regs 25 = Z_to_bv 64 (ab + rz + n) ->
  0 <= ia -> ia + 4096 < 2 ^ 64 -> 8192 <= ab -> ab + nd + 8192 < 2 ^ 48 -> ab mod 4096 = 0 -> 16 <= rz <= 2048 -> 8 <= n < 2 ^ 40 -> n + rz <= nd -> 0 <= id < 2 ^ 32 ->
  4096 * (q - 1) < nd <= 4096 * q -> 0 <= spb -> spb + 2 ^ 37 < 2 ^ 48 -> (ab < spb \/ spb + 2 ^ 37 <= ab) ->
  wrA M (ab + rz - 16) 16 -> cellA M (ia + 32) 8 spb -> cellA M (ia + 64) 8 4096 -> cellA M (ab - 4096 + 16) 8 nd ->
  apart (ab + rz - 16) 16 (ia + 32) 40 -> apart (ab + rz - 16) 16 (ab - 4096 + 16) 8 ->
  exists regs',
    msteps ASEGS (mkst regs (0x5b4a4 : word) M rom) (mkst regs' (0x839b4 : word) (Wn 8 M (ab + rz - 8) id) rom)
    /\ getr regs' 1 = (0x5b57c : bv 64)%bv /\ getr regs' 10 = Z_to_bv 64 ab /\ getr regs' 11 = Z_to_bv 64 rz /\ getr regs' 12 = Z_to_bv 64 250
    /\ getr regs' 8 = Z_to_bv 64 (4096 * q) /\ getr regs' 22 = Z_to_bv 64 ((ab + rz + n + 7) / 8 * 8)
    /\ (forall x : reg, x <> 1%bv -> x <> 8%bv -> x <> 10%bv -> x <> 11%bv -> x <> 12%bv -> x <> 22%bv -> x <> 25%bv -> getr regs' x = getr regs x).
Proof.
  intros regs M rom ia ab n rz id nd q spb H10 H8 H9 H18 H20 H21 H22 H24 H25 Hia Hia' Hab Hab' Hab4 Hrz Hn Hnd Hid Hq Hspb Hspb' OUT W Cspb Cpg Cnd A1 A2.
  (* [comment removed for export] *)
  assert (S1 : exists r1, msteps ASEGS (mkst regs (0x5b4a4 : word) M rom) (mkst r1 (0x5b4d4 : word) (Wn 8 M (ab + rz - 8) id) rom)
                 /\ (forall x : reg, x <> 10%bv -> getr r1 x = getr regs x)).
  { eexists. split.
    - stepn F_5b45c D_5b45c. rwH. rewrite art_zb_slli by lia.
      stepn F_5b460 D_5b460. rwH. rewrite (art_zb_srli_exact _ 32 id) by lia.
      stepn F_5b464 D_5b464. rwH. unfold v_or. rewrite !art_u_lit by lia. rewrite Z.lor_0_l.
      zsd F_5b468 D_5b468 (ab + rz - 16 + 8) id ltac:(rewok W).
      zbtk F_5b46c D_5b46c. replace (ab + rz - 16 + 8) with (ab + rz - 8) by lia. apply mst_refl.
    - intros; kept_solve. }
  destruct S1 as (r1 & RUN1 & K1).
  set (M1 := Wn 8 M (ab + rz - 8) id) in *.
  assert (Cspb1 : cellA M1 (ia + 32) 8 spb) by (unfold M1; apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart in *; cbn; lia|exact Cspb]).
  assert (Cpg1 : cellA M1 (ia + 64) 8 4096) by (unfold M1; apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart in *; cbn; lia|exact Cpg]).
  assert (Cnd1 : cellA M1 (ab - 4096 + 16) 8 nd) by (unfold M1; apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart in *; cbn; lia|exact Cnd]).
  (* [comment removed for export] *)
  destruct (art_alloc_csec_range r1 M1 rom ia ab spb ltac:(rewrite K1 by discriminate; exact H18) ltac:(rewrite K1 by discriminate; exact H22)
              Hia Hia' ltac:(lia) Hspb Hspb' OUT Cspb1) as (r2 & RUN2 & K2).
  assert (KK : forall x : reg, x <> 10%bv -> x <> 11%bv -> getr r2 x = getr regs x).
  { intros x N10 N11. rewrite K2 by assumption. apply K1. exact N10. }
  assert (Q18 : getr r2 18 = Z_to_bv 64 ab) by (rewrite KK by discriminate; exact H18).
  assert (Q20 : getr r2 20 = Z_to_bv 64 (ab + rz)) by (rewrite KK by discriminate; exact H20).
  assert (Q22 : getr r2 22 = Z_to_bv 64 ia) by (rewrite KK by discriminate; exact H22).
  assert (Q25 : getr r2 25 = Z_to_bv 64 (ab + rz + n)) by (rewrite KK by discriminate; exact H25).
  (* [comment removed for export] *)
  assert (E4096 : Z.land 4095 ab = 0).
  { rewrite Z.land_comm. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. exact Hab4. }
  assert (Erup : Z.land (nd + 4095) (2 ^ 64 - 2 ^ 12) = 4096 * q).
  { rewrite sa_land_down by lia. change (2 ^ 12) with 4096.
    assert (E : (nd + 4095) mod 4096 = nd + 4095 - 4096 * q). { symmetry. apply (Z.mod_unique_pos _ _ q); lia. }
    rewrite E. lia. }
  assert (S3 : exists r3, msteps ASEGS (mkst r2 (0x5b510 : word) M1 rom) (mkst r3 (0x839b4 : word) M1 rom)
                 /\ getr r3 1 = (0x5b57c : bv 64)%bv /\ getr r3 10 = Z_to_bv 64 ab /\ getr r3 11 = Z_to_bv 64 rz /\ getr r3 12 = Z_to_bv 64 250
                 /\ getr r3 8 = Z_to_bv 64 (4096 * q) /\ getr r3 22 = Z_to_bv 64 ((ab + rz + n + 7) / 8 * 8)
                 /\ (forall x : reg, x <> 1%bv -> x <> 8%bv -> x <> 10%bv -> x <> 11%bv -> x <> 12%bv -> x <> 22%bv -> x <> 25%bv -> getr r3 x = getr r2 x)).
  { eexists. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
    - zld F_5b4c8 D_5b4c8 (ia + 64) Cpg1.
      zstep F_5b4cc D_5b4cc.
      stepn F_5b4d0 D_5b4d0. rwH. rewrite art_zb_and by lia. rewrite E4096.
      zbft F_5b4d4 D_5b4d4.
      stepn F_5b4d8 D_5b4d8. rwH.
      zbft F_5b4dc D_5b4dc.
      zstep F_5b4e0 D_5b4e0.
      zld F_5b4e4 D_5b4e4 (ab - 4096 + 16) Cnd1.
      zstep F_5b4e8 D_5b4e8.
      zstep F_5b4ec D_5b4ec.
      stepn F_5b4f0 D_5b4f0. rwH. rewrite art_zb_and by lia. change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite Erup.
      stepn F_5b4f4 D_5b4f4.
      zstep F_5b51c D_5b51c.
      stepn F_5b520 D_5b520. rwH. unfold v_andi. rewrite (art_u_lit (ab + rz + n + 7)) by lia. change (bv_wrap 64 (-8)) with 18446744073709551608. rewrite art_land_m8 by lia.
      zstep F_5b524 D_5b524. replace (ab + rz - ab) with rz by lia.
      zstep F_5b528 D_5b528. zstep F_5b52c D_5b52c.
      stepn F_5b530 D_5b530.
      apply mst_refl.
    - gres. apply bv_eq. reflexivity.
    - kept_solve. - kept_solve. - kept_solve. - kept_solve. - kept_solve.
    - intros; kept_solve. }
  destruct S3 as (r3 & RUN3 & X1 & X10 & X11 & X12 & X8 & X22 & K3).
  exists r3. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]; try assumption.
  - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
  - intros x N1 N8 N10 N11 N12 N22 N25. rewrite K3 by assumption. apply KK; assumption.
Qed.

Lemma art_alloc_csec2 : forall regs (M rom : word -> option byte) (ab tb q : Z),
  getr regs 18 = Z_to_bv 64 ab -> getr regs 22 = Z_to_bv 64 tb -> getr regs 8 = Z_to_bv 64 (4096 * q) ->
  0 <= ab -> 0 <= tb -> tb <= ab + 4096 * q -> ab + 4096 * q < 2 ^ 47 ->
  msteps ASEGS (mkst regs (0x5b57c : word) M rom)
               (mkst (regupd (regupd (regupd (regupd regs 1 (0x5b590 : bv 64)%bv) 10 (Z_to_bv 64 tb)) 11 (Z_to_bv 64 (ab + 4096 * q - tb))) 12 (Z_to_bv 64 250)) (0x839b4 : word) M rom).
Proof.
  intros regs M rom ab tb q H18 H22 H8 Hab Htb Hle Hhi.
  zstep F_5b534 D_5b534. zstep F_5b538 D_5b538. zstep F_5b53c D_5b53c. zstep F_5b540 D_5b540.
  stepn F_5b544 D_5b544.
  replace (ab - tb + 4096 * q) with (ab + 4096 * q - tb) by lia.
  zret.
Qed.

Lemma art_alloc_csec3 : forall regs (M rom : word -> option byte) (ab n rz : Z),
  getr regs 9 = Z_to_bv 64 n -> getr regs 20 = Z_to_bv 64 (ab + rz) ->
  0 <= ab -> ab + rz < 2 ^ 47 -> 0 <= rz -> 8 <= n < 2 ^ 40 ->
  msteps ASEGS (mkst regs (0x5b590 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd regs 1 (0x5b5b0 : bv 64)%bv) 10 (Z_to_bv 64 (ab + rz))) 11 (Z_to_bv 64 (n / 8 * 8))) 12 (Z_to_bv 64 0)) 22 (Z_to_bv 64 (n / 8 * 8))) (0x839b4 : word) M rom).
Proof.
  intros regs M rom ab n rz H9 H20 Hab Hab' Hrz Hn.
  zstep F_5b548 D_5b548. zstep F_5b54c D_5b54c.
  stepn F_5b550 D_5b550. rwH. rewrite art_zb_and by lia. rewrite art_land_m8_48 by lia.
  assert (8 <= n / 8 * 8). { pose proof (Z.div_le_mono 8 n 8 ltac:(lia) ltac:(lia)) as D. change (8 / 8) with 1 in D. lia. }
  pose proof (Z.mul_div_le n 8 ltac:(lia)).
  zbft F_5b554 D_5b554.
  zstep F_5b558 D_5b558. zstep F_5b55c D_5b55c. zstep F_5b560 D_5b560.
  stepn F_5b564 D_5b564.
  zret.
Qed.
End FPX.
