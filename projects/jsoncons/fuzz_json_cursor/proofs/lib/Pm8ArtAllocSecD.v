(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac Pm8ArtLeaf Pm8ArtPoison Pm8ArtAllocC Pm8ArtAllocD Pm8ArtAllocV.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm8_code_59000_5a000.
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
  art_layout M -> cellA M (0x15a1b8 + 85) 1 1 -> (n mod 8 <> 0 -> wrA M (art_d1_addr ab rz n) 1) ->
  exists regs',
    msteps ASEGS (mkst regs (0x59914 : word) M rom) (mkst regs' (0x599a8 : word) (art_d1_mem M ab rz n) rom)
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
      * zbft F_598c4 D_598c4.
        stepn F_598c8 D_598c8.
        zcall (art_can_poison_fn _ _ _ _).
        zbft F_598cc D_598cc.
        zstep F_598d0 D_598d0. zld F_598d4 D_598d4 0x153138 G48. zld F_598d8 D_598d8 0x15c9b8 Csb. unfold SB.
        zstep F_598dc D_598dc. zstep F_598e0 D_598e0. zstep F_598e4 D_598e4. zstep F_598e8 D_598e8. zstep F_598ec D_598ec.
        zbtk F_598f0 D_598f0.
        zstep F_59934 D_59934. zld F_59938 D_59938 0x153130 G40.
        zlbu F_5993c D_5993c (0x15a1b8 + 85) Cpp.
        stepn F_59940 D_59940. rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
        zstep F_59944 D_59944. zstep F_59948 D_59948.
        stepn F_5994c D_5994c. rwH. rewrite art_zb_and by lia. rewrite art_land_full_r by lia.
        stepn F_59950 D_59950. rwH. rewrite art_zb_andi by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
        zsb F_59954 D_59954 (2147450880 + (ab + rz + n / 8 * 8) / 8) (n mod 8) ltac:(rewok Wsh).
        apply mst_refl.
      * intros r Hr. unfold art_d1_kept in Hr. decompose [and] Hr. kept_solve.
    + eexists. split.
      * zbft F_598c4 D_598c4.
        stepn F_598c8 D_598c8.
        zcall (art_can_poison_fn _ _ _ _).
        zbft F_598cc D_598cc.
        zstep F_598d0 D_598d0. zld F_598d4 D_598d4 0x153138 G48. zld F_598d8 D_598d8 0x15c9b8 Csb. unfold SB.
        zstep F_598dc D_598dc. zstep F_598e0 D_598e0. zstep F_598e4 D_598e4. zstep F_598e8 D_598e8. zstep F_598ec D_598ec.
        zbft F_598f0 D_598f0.
        zstep F_598f4 D_598f4. zld F_598f8 D_598f8 0x153140 G50. zstep F_598fc D_598fc. zld F_59900 D_59900 0x153148 G58.
        zld F_59904 D_59904 0x15d6a8 Cmb. zld F_59908 D_59908 0x15d6b0 Cme.
        zstep F_5990c D_5990c.
        zbtk F_59910 D_59910.
        zstep F_59918 D_59918. zld F_5991c D_5991c 0x153150 G60. zld F_59920 D_59920 0x15d6a0 Che. unfold kHighMemEnd.
        zstep F_59924 D_59924. zstep F_59928 D_59928.
        zbft F_5992c D_5992c. zbft F_59930 D_59930.
        zstep F_59934 D_59934. zld F_59938 D_59938 0x153130 G40.
        zlbu F_5993c D_5993c (0x15a1b8 + 85) Cpp.
        stepn F_59940 D_59940. rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
        zstep F_59944 D_59944. zstep F_59948 D_59948.
        stepn F_5994c D_5994c. rwH. rewrite art_zb_and by lia. rewrite art_land_full_r by lia.
        stepn F_59950 D_59950. rwH. rewrite art_zb_andi by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
        zsb F_59954 D_59954 (2147450880 + (ab + rz + n / 8 * 8) / 8) (n mod 8) ltac:(rewok Wsh).
        apply mst_refl.
      * intros r Hr. unfold art_d1_kept in Hr. decompose [and] Hr. kept_solve.
Qed.

Definition art_d2_large_mem (M : word -> option byte) (sp t n nd mc mb mr ml : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) 0x599ac) (sp - 24) 0x89c9c) (t + 2800) (mc + 1)) (t + 2800 + 8) (mb + n)) (t + 2800 + 16) (mr + (nd - n)))
       (t + 2800 + 104) (ml + 1).

Definition art_d2_kept (r : reg) : Prop :=
  r <> 1%bv /\ r <> 10%bv /\ r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv.

Lemma art_alloc_d2_large_fn : forall regs (M rom : word -> option byte) (sp ab n nd rz tp key tsd ctx t mc mb mr ml : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> getr regs 9 = Z_to_bv 64 n -> getr regs 19 = Z_to_bv 64 nd -> getr regs 20 = Z_to_bv 64 (ab + rz) ->
  32 <= sp -> sp + 128 < 2 ^ 64 -> 0x6b3000 + 32 <= sp -> 4096 <= n -> n <= nd -> 65536 < nd < 2 ^ 40 -> 0 <= ab + rz < 2 ^ 64 ->
  0 <= mc < 2 ^ 64 -> 0 <= mb < 2 ^ 64 -> 0 <= mr < 2 ^ 64 -> 0 <= ml < 2 ^ 64 ->
  wrA M (sp - 32) 32 -> art_tsd M tp key tsd ctx t -> 4096 <= t -> t + 4096 < 2 ^ 64 -> (t + 4096 <= 0x10000 \/ 0x6b3000 <= t) ->
  apart (sp - 32) 32 0x15c220 8 -> apart (sp - 32) 32 (tp - 88) 8 -> apart (sp - 32) 32 (tsd + 8 * key) 8 -> apart (sp - 32) 32 (ctx + 152) 8 ->
  apart (sp - 32) 160 (t + 2800) 112 ->
  cellA M (t + 2800) 8 mc -> cellA M (t + 2800 + 8) 8 mb -> cellA M (t + 2800 + 16) 8 mr -> cellA M (t + 2800 + 104) 8 ml -> wrA M (t + 2800) 112 ->
  cellA M (sp + 8) 8 1 -> art_layout M -> cellA M (0x15a1b8 + 44) 4 4096 -> cellA M (0x15a1b8 + 52) 4 190 ->
  exists regs',
    msteps ASEGS (mkst regs (0x599a8 : word) M rom) (mkst regs' (0x145308 : word) (art_d2_large_mem M sp t n nd mc mb mr ml) rom)
    /\ getr regs' 1 = (0x59b3c : bv 64)%bv /\ getr regs' 10 = Z_to_bv 64 (ab + rz) /\ getr regs' 11 = Z_to_bv 64 190 /\ getr regs' 12 = Z_to_bv 64 4096
    /\ (forall r : reg, art_d2_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp ab n nd rz tp key tsd ctx t mc mb mr ml H2 H4 H9 H19 H20 Hsp Hsp' IMG Hn Hnd Hnd' Hub Hmc Hmb Hmr Hml
         W TSD Ht Ht' Timg A1 A2 A3 A4 A5 Cmc Cmb Cmr Cml Wts Ccf L Cmax Cfb.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  pose proof L as (G48 & Csb & G50 & Cmb0 & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
  unfold art_d2_large_mem.
  eexists. split; [|split; [|split; [|split; [|split]]]].
  - stepn F_59958 D_59958.
    zcall (art_thread_stats_fn _ _ _ _ sp tp key tsd ctx t).
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (Cmc' : cellA X (t + 2800) 8 mc) by (unfold apart in *; recell Cmc);
      assert (Cmb' : cellA X (t + 2800 + 8) 8 mb) by (unfold apart in *; recell Cmb);
      assert (Cmr' : cellA X (t + 2800 + 16) 8 mr) by (unfold apart in *; recell Cmr);
      assert (Wts' : wrA X (t + 2800) 112) by (repeat apply wr_Wn; exact Wts) end.
    zld F_5995c D_5995c (t + 2800 + 16) Cmr'.
    zld F_59960 D_59960 (t + 2800) Cmc'.
    zld F_59964 D_59964 (t + 2800 + 8) Cmb'.
    zstep F_59968 D_59968. zstep F_5996c D_5996c. zstep F_59970 D_59970. zstep F_59974 D_59974. zstep F_59978 D_59978. zstep F_5997c D_5997c.
    zsd F_59980 D_59980 (t + 2800) (mc + 1) ltac:(rewok Wts').
    zsd F_59984 D_59984 (t + 2800 + 8) (mb + n) ltac:(rewok Wts').
    zsd F_59988 D_59988 (t + 2800 + 16) (mr + (nd - n)) ltac:(rewok Wts').
    zbft F_5998c D_5998c.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cml' : cellA X (t + 2800 + 104) 8 ml) by (unfold apart in *; recell Cml) end.
    zld F_59990 D_59990 (t + 2800 + 104) Cml'.
    zstep F_59994 D_59994.
    zsd F_59998 D_59998 (t + 2800 + 104) (ml + 1) ltac:(rewok Wts').
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (Ccf' : cellA X (sp + 8) 8 1) by (unfold apart in *; recell Ccf);
      assert (G40' : cellA X 0x153130 8 0x15a1b8) by (unfold apart in *; recell G40);
      assert (Cmax' : cellA X (0x15a1b8 + 44) 4 4096) by (unfold apart in *; recell Cmax);
      assert (G68' : cellA X 0x153158 8 0x155160) by (unfold apart in *; recell G68);
      assert (Crm' : cellA X 0x155160 8 0x145308) by (unfold apart in *; recell Crm);
      assert (Cfb' : cellA X (0x15a1b8 + 52) 4 190) by (unfold apart in *; recell Cfb) end.
    zld F_5999c D_5999c (sp + 8) Ccf'.
    zbtk F_599a0 D_599a0.
    zstep F_59ab8 D_59ab8. zld F_59abc D_59abc 0x153130 G40'.
    zlw F_59ac0 D_59ac0 (0x15a1b8 + 44) Cmax'.
    zbft F_59ac4 D_59ac4.
    zstep F_59ac8 D_59ac8.
    zbft F_59acc D_59acc.
    zstep F_59ad0 D_59ad0.
    zstep F_59ad4 D_59ad4. zld F_59ad8 D_59ad8 0x153158 G68'. zld F_59adc D_59adc 0x155160 Crm'.
    zlw F_59ae0 D_59ae0 (0x15a1b8 + 52) Cfb'.
    zstep F_59ae4 D_59ae4.
    stepjr F_59ae8 D_59ae8 (0x145308 : bv 64)%bv ltac:(gres; bveq).
    apply mst_refl.
  - gres. apply bv_eq. reflexivity.
  - kept_solve.
  - kept_solve.
  - kept_solve.
  - intros r Hr. unfold art_d2_kept in Hr. decompose [and] Hr. kept_solve.
Qed.
End FPX.
