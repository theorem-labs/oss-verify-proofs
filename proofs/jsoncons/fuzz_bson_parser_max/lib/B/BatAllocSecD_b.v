(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatPoison_b BatAllocC_b BatAllocD_b BatAllocV_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r3cf10_3de98_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
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
  art_layout M -> cellA M (0x13d438 + 85) 1 1 -> (n mod 8 <> 0 -> wrA M (art_d1_addr ab rz n) 1) ->
  exists regs',
    msteps ASEGS (mkst regs (0x52a9c : word) M rom) (mkst regs' (0x52b30 : word) (art_d1_mem M ab rz n) rom)
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
      * zbft F_52684 D_52684.
        stepn F_52688 D_52688.
        zcall (art_can_poison_fn _ _ _ _).
        zbft F_5268c D_5268c.
        zstep F_52690 D_52690. zld F_52694 D_52694 0x1374c0 G48. zld F_52698 D_52698 0x13fc38 Csb. unfold SB.
        zstep F_5269c D_5269c. zstep F_526a0 D_526a0. zstep F_526a4 D_526a4. zstep F_526a8 D_526a8. zstep F_526ac D_526ac.
        zbtk F_526b0 D_526b0.
        zstep F_526f4 D_526f4. zld F_526f8 D_526f8 0x1374b8 G40.
        zlbu F_526fc D_526fc (0x13d438 + 85) Cpp.
        stepn F_52700 D_52700. rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
        zstep F_52704 D_52704. zstep F_52708 D_52708.
        stepn F_5270c D_5270c. rwH. rewrite art_zb_and by lia. rewrite art_land_full_r by lia.
        stepn F_52710 D_52710. rwH. rewrite art_zb_andi by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
        zsb F_52714 D_52714 (2147450880 + (ab + rz + n / 8 * 8) / 8) (n mod 8) ltac:(rewok Wsh).
        apply mst_refl.
      * intros r Hr. unfold art_d1_kept in Hr. decompose [and] Hr. kept_solve.
    + eexists. split.
      * zbft F_52684 D_52684.
        stepn F_52688 D_52688.
        zcall (art_can_poison_fn _ _ _ _).
        zbft F_5268c D_5268c.
        zstep F_52690 D_52690. zld F_52694 D_52694 0x1374c0 G48. zld F_52698 D_52698 0x13fc38 Csb. unfold SB.
        zstep F_5269c D_5269c. zstep F_526a0 D_526a0. zstep F_526a4 D_526a4. zstep F_526a8 D_526a8. zstep F_526ac D_526ac.
        zbft F_526b0 D_526b0.
        zstep F_526b4 D_526b4. zld F_526b8 D_526b8 0x1374c8 G50. zstep F_526bc D_526bc. zld F_526c0 D_526c0 0x1374d0 G58.
        zld F_526c4 D_526c4 0x140928 Cmb. zld F_526c8 D_526c8 0x140930 Cme.
        zstep F_526cc D_526cc.
        zbtk F_526d0 D_526d0.
        zstep F_526d8 D_526d8. zld F_526dc D_526dc 0x1374d8 G60. zld F_526e0 D_526e0 0x140920 Che. unfold kHighMemEnd.
        zstep F_526e4 D_526e4. zstep F_526e8 D_526e8.
        zbft F_526ec D_526ec. zbft F_526f0 D_526f0.
        zstep F_526f4 D_526f4. zld F_526f8 D_526f8 0x1374b8 G40.
        zlbu F_526fc D_526fc (0x13d438 + 85) Cpp.
        stepn F_52700 D_52700. rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
        zstep F_52704 D_52704. zstep F_52708 D_52708.
        stepn F_5270c D_5270c. rwH. rewrite art_zb_and by lia. rewrite art_land_full_r by lia.
        stepn F_52710 D_52710. rwH. rewrite art_zb_andi by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
        zsb F_52714 D_52714 (2147450880 + (ab + rz + n / 8 * 8) / 8) (n mod 8) ltac:(rewok Wsh).
        apply mst_refl.
      * intros r Hr. unfold art_d1_kept in Hr. decompose [and] Hr. kept_solve.
Qed.

Definition art_d2_large_mem (M : word -> option byte) (sp t n nd mc mb mr ml : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) 0x52b34) (sp - 24) 0x82abc) (t + 2800) (mc + 1)) (t + 2800 + 8) (mb + n)) (t + 2800 + 16) (mr + (nd - n)))
       (t + 2800 + 104) (ml + 1).

Definition art_d2_kept (r : reg) : Prop :=
  r <> 1%bv /\ r <> 10%bv /\ r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv.

#[using="Type"] Lemma art_alloc_d2_large_fn : forall regs (M rom : word -> option byte) (sp ab n nd rz tp key tsd ctx t mc mb mr ml : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> getr regs 9 = Z_to_bv 64 n -> getr regs 19 = Z_to_bv 64 nd -> getr regs 20 = Z_to_bv 64 (ab + rz) ->
  32 <= sp -> sp + 128 < 2 ^ 64 -> 0x696000 + 32 <= sp -> 4096 <= n -> n <= nd -> 65536 < nd < 2 ^ 40 -> 0 <= ab + rz < 2 ^ 64 ->
  0 <= mc < 2 ^ 64 -> 0 <= mb < 2 ^ 64 -> 0 <= mr < 2 ^ 64 -> 0 <= ml < 2 ^ 64 ->
  wrA M (sp - 32) 32 -> art_tsd M tp key tsd ctx t -> 4096 <= t -> t + 4096 < 2 ^ 64 -> (t + 4096 <= 0x10000 \/ 0x696000 <= t) ->
  apart (sp - 32) 32 0x13f4a0 8 -> apart (sp - 32) 32 (tp - 88) 8 -> apart (sp - 32) 32 (tsd + 8 * key) 8 -> apart (sp - 32) 32 (ctx + 152) 8 ->
  apart (sp - 32) 160 (t + 2800) 112 ->
  cellA M (t + 2800) 8 mc -> cellA M (t + 2800 + 8) 8 mb -> cellA M (t + 2800 + 16) 8 mr -> cellA M (t + 2800 + 104) 8 ml -> wrA M (t + 2800) 112 ->
  cellA M (sp + 8) 8 1 -> art_layout M -> cellA M (0x13d438 + 44) 4 4096 -> cellA M (0x13d438 + 52) 4 190 ->
  exists regs',
    msteps ASEGS (mkst regs (0x52b30 : word) M rom) (mkst regs' (0x129d04 : word) (art_d2_large_mem M sp t n nd mc mb mr ml) rom)
    /\ getr regs' 1 = (0x52cc4 : bv 64)%bv /\ getr regs' 10 = Z_to_bv 64 (ab + rz) /\ getr regs' 11 = Z_to_bv 64 190 /\ getr regs' 12 = Z_to_bv 64 4096
    /\ (forall r : reg, art_d2_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp ab n nd rz tp key tsd ctx t mc mb mr ml H2 H4 H9 H19 H20 Hsp Hsp' IMG Hn Hnd Hnd' Hub Hmc Hmb Hmr Hml
         W TSD Ht Ht' Timg A1 A2 A3 A4 A5 Cmc Cmb Cmr Cml Wts Ccf L Cmax Cfb.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  pose proof L as (G48 & Csb & G50 & Cmb0 & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
  unfold art_d2_large_mem.
  eexists. split; [|split; [|split; [|split; [|split]]]].
  - stepn F_52718 D_52718.
    zcall (art_thread_stats_fn _ _ _ _ sp tp key tsd ctx t).
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (Cmc' : cellA X (t + 2800) 8 mc) by (unfold apart in *; recell Cmc);
      assert (Cmb' : cellA X (t + 2800 + 8) 8 mb) by (unfold apart in *; recell Cmb);
      assert (Cmr' : cellA X (t + 2800 + 16) 8 mr) by (unfold apart in *; recell Cmr);
      assert (Wts' : wrA X (t + 2800) 112) by (repeat apply wr_Wn; exact Wts) end.
    zld F_5271c D_5271c (t + 2800 + 16) Cmr'.
    zld F_52720 D_52720 (t + 2800) Cmc'.
    zld F_52724 D_52724 (t + 2800 + 8) Cmb'.
    zstep F_52728 D_52728. zstep F_5272c D_5272c. zstep F_52730 D_52730. zstep F_52734 D_52734. zstep F_52738 D_52738. zstep F_5273c D_5273c.
    zsd F_52740 D_52740 (t + 2800) (mc + 1) ltac:(rewok Wts').
    zsd F_52744 D_52744 (t + 2800 + 8) (mb + n) ltac:(rewok Wts').
    zsd F_52748 D_52748 (t + 2800 + 16) (mr + (nd - n)) ltac:(rewok Wts').
    zbft F_5274c D_5274c.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cml' : cellA X (t + 2800 + 104) 8 ml) by (unfold apart in *; recell Cml) end.
    zld F_52750 D_52750 (t + 2800 + 104) Cml'.
    zstep F_52754 D_52754.
    zsd F_52758 D_52758 (t + 2800 + 104) (ml + 1) ltac:(rewok Wts').
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (Ccf' : cellA X (sp + 8) 8 1) by (unfold apart in *; recell Ccf);
      assert (G40' : cellA X 0x1374b8 8 0x13d438) by (unfold apart in *; recell G40);
      assert (Cmax' : cellA X (0x13d438 + 44) 4 4096) by (unfold apart in *; recell Cmax);
      assert (G68' : cellA X 0x1374e0 8 0x1394d0) by (unfold apart in *; recell G68);
      assert (Crm' : cellA X 0x1394d0 8 0x129d04) by (unfold apart in *; recell Crm);
      assert (Cfb' : cellA X (0x13d438 + 52) 4 190) by (unfold apart in *; recell Cfb) end.
    zld F_5275c D_5275c (sp + 8) Ccf'.
    zbtk F_52760 D_52760.
    zstep F_52878 D_52878. zld F_5287c D_5287c 0x1374b8 G40'.
    zlw F_52880 D_52880 (0x13d438 + 44) Cmax'.
    zbft F_52884 D_52884.
    zstep F_52888 D_52888.
    zbft F_5288c D_5288c.
    zstep F_52890 D_52890.
    zstep F_52894 D_52894. zld F_52898 D_52898 0x1374e0 G68'. zld F_5289c D_5289c 0x1394d0 Crm'.
    zlw F_528a0 D_528a0 (0x13d438 + 52) Cfb'.
    zstep F_528a4 D_528a4.
    stepjr F_528a8 D_528a8 (0x129d04 : bv 64)%bv ltac:(gres; bveq).
    apply mst_refl.
  - gres. apply bv_eq. reflexivity.
  - kept_solve.
  - kept_solve.
  - kept_solve.
  - intros r Hr. unfold art_d2_kept in Hr. decompose [and] Hr. kept_solve.
Qed.
End FPX.
