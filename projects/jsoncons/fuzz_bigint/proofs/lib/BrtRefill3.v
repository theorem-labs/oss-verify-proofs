(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac BrtLeaf BrtAllocG BrtCachePop BrtCombAlloc BrtCombAllocHit BrtClassId BrtFree1 BrtRefill1 BrtRefill2.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import Bo0_code_4183c_42d28.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Set Printing Depth 1000000. Set Printing Width 10000.
Ltac showst := lazymatch goal with |- msteps _ (mkst ?R ?P ?MM _) _ => idtac "REGS" R; idtac "PC" P; idtac "MEM" MM | |- ?G => idtac "GOAL" G end; fail "SHOWST".


Ltac zlhu F D a HYP :=
  chain_step; [reflexivity | eapply step_lhu; [exact F | reflexivity | exact D | zaddr a; exact HYP | apply art_bytes2; lia ] | step_simpl; vnorm].




Lemma art_srliw_small : forall x k, 0 <= x < 2 ^ 31 -> 0 <= k -> v_srliw (Z_to_bv 64 x) k = Z_to_bv 64 (x / 2 ^ k).
Proof.
  intros x k Hx Hk. unfold v_srliw. rewrite art_u_lit by lia. f_equal.
  unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). rewrite (Z.mod_small x) by lia. rewrite Z.shiftr_div_pow2 by lia.
  assert (0 <= x / 2 ^ k <= x). { split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. rewrite <- (Z.mul_1_l x) at 1. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.pow_le_mono_r with (b := 0) || idtac; pose proof (Z.pow_pos_nonneg 2 k); lia. }
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32). rewrite Z.mod_small by lia. lia.
Qed.

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Lemma art_refill_a_fn : forall regs (M rom : word -> option byte) (raw : word) (sp ca c ia mc : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 ca -> getr regs 11 = Z_to_bv 64 (ca + 80 * c) -> getr regs 12 = Z_to_bv 64 ia -> getr regs 13 = Z_to_bv 64 c ->
  32 <= sp -> sp < 2 ^ 64 -> 0x634000 + 32 <= sp -> 4096 <= ca -> ca + 4096 < 2 ^ 64 -> 1 <= c <= 31 -> 0 <= ia < 2 ^ 64 -> 2 <= mc <= 16 ->
  apart (sp - 32) 32 ca 4096 ->
  wrA M (sp - 32) 32 -> cellA M (ca + 80 * c + 4) 4 mc ->
  msteps ASEGS (mkst regs (0x42498 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x424d8 : bv 64)%bv) 2 (Z_to_bv 64 (sp - 32))) 8 (Z_to_bv 64 (ca + 80 * c))) 9 (Z_to_bv 64 (mc / 2))) 10 (Z_to_bv 64 ia)) 11 (Z_to_bv 64 (ca + 2560))) 12 (Z_to_bv 64 c)) 13 (Z_to_bv 64 (ca + 80 * c + 16))) 14 (Z_to_bv 64 (mc / 2)))
          (0x42598 : word) (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) rom).
Proof.
  intros regs M rom raw sp ca c ia mc H1 H2 H10 H11 H12 H13 Hsp Hsp' IMG Hca Hca' Hc Hia Hmc A W Cmc.
  zstep F_42498 D_42498.
  zsd F_4249c D_4249c (sp - 8) (U raw) ltac:(rewok W). zsd F_424a0 D_424a0 (sp - 16) (U (getr regs 8)) ltac:(rewok W). zsd F_424a4 D_424a4 (sp - 24) (U (getr regs 9)) ltac:(rewok W).
  zstep F_424a8 D_424a8. zstep F_424ac D_424ac.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cmc' : cellA X (ca + 80 * c + 4) 4 mc) by (unfold apart in A; zcell) end.
  zlw F_424b0 D_424b0 (ca + 80 * c + 4) Cmc'.
  zbft F_424b4 D_424b4.
  stepn F_424b8 D_424b8. rwH. rewrite art_srliw_small by lia. change (2 ^ 1) with 2.
  zstep F_424bc D_424bc. zstep F_424c0 D_424c0. zstep F_424c4 D_424c4. zstep F_424c8 D_424c8. zstep F_424cc D_424cc. zstep F_424d0 D_424d0.
  stepn F_424d4 D_424d4.
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_refill_b_fn : forall regs (M rom : word -> option byte) (raw : word) (sp pcp n g8 g9 : Z),
  getr regs 2 = Z_to_bv 64 (sp - 32) -> getr regs 8 = Z_to_bv 64 pcp -> getr regs 9 = Z_to_bv 64 n -> getr regs 10 = Z_to_bv 64 1 ->
  32 <= sp -> sp < 2 ^ 64 -> 4096 <= pcp -> pcp + 80 < 2 ^ 64 -> 0 <= n < 2 ^ 31 -> ret_ok raw -> 0 <= g8 < 2 ^ 64 -> 0 <= g9 < 2 ^ 64 -> apart (sp - 32) 32 pcp 80 ->
  wrA M pcp 4 -> cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 g8 -> cellA M (sp - 24) 8 g9 ->
  msteps ASEGS (mkst regs (0x424d8 : word) M rom) (mkst (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (Z_to_bv 64 g8)) 9 (Z_to_bv 64 g9)) raw (Wn 4 M pcp n) rom).
Proof.
  intros regs M rom raw sp pcp n g8 g9 H2 H8 H9 H10 Hsp Hsp' Hp Hp' Hn Hret Hg8 Hg9 A W C8 C16 C24.
  zbft F_424d8 D_424d8.
  zsw F_424dc D_424dc pcp n ltac:(rewok W).
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C8' : cellA X (sp - 8) 8 (U raw)) by (unfold apart in A; zcell); assert (C16' : cellA X (sp - 16) 8 g8) by (unfold apart in A; zcell);
                                                   assert (C24' : cellA X (sp - 24) 8 g9) by (unfold apart in A; zcell) end.
  zld F_424e0 D_424e0 (sp - 8) C8'. rewrite Z_to_bv_bv_unsigned.
  zld F_424e4 D_424e4 (sp - 16) C16'. zld F_424e8 D_424e8 (sp - 24) C24'.
  zstep F_424ec D_424ec.
  stepret F_424f0 D_424f0 raw ltac:(rwH; reflexivity).
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_miss_a_fn : forall regs (M rom : word -> option byte) (c ca ia al : Z),
  getr regs 8 = Z_to_bv 64 c -> getr regs 10 = Z_to_bv 64 ia -> getr regs 11 = Z_to_bv 64 ca -> getr regs 13 = Z_to_bv 64 al ->
  1 <= c <= 31 -> 0 <= ca -> ca + 4096 < 2 ^ 64 -> 0 <= ia < 2 ^ 64 -> 0 <= al < 2 ^ 64 ->
  cellA M (ca + 80 * c) 4 0 ->
  msteps ASEGS (mkst regs (0x41edc : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x41ff8 : bv 64)%bv) 9 (Z_to_bv 64 (ca + 80 * c))) 10 (Z_to_bv 64 ca)) 11 (Z_to_bv 64 (ca + 80 * c))) 12 (Z_to_bv 64 ia)) 13 (Z_to_bv 64 c)) 18 (Z_to_bv 64 al)) 19 (Z_to_bv 64 ca)) 20 (Z_to_bv 64 ia))
          (0x42498 : word) M rom).
Proof.
  intros regs M rom c ca ia al H8 H10 H11 H13 Hc Hca Hca' Hia Hal Ccnt.
  zbft F_41edc D_41edc.
  zstep F_41ee0 D_41ee0.
  zbft F_41ee4 D_41ee4.
  zstep F_41ee8 D_41ee8. zstep F_41eec D_41eec. zstep F_41ef0 D_41ef0.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Ccnt' : cellA X (ca + c * 80) 4 0) by (replace (ca + c * 80) with (ca + 80 * c) by lia; exact Ccnt) end.
  zlw F_41ef4 D_41ef4 (ca + c * 80) Ccnt'.
  zbtk F_41ef8 D_41ef8.
  zstep F_41fd8 D_41fd8. zstep F_41fdc D_41fdc. zstep F_41fe0 D_41fe0. zstep F_41fe4 D_41fe4. zstep F_41fe8 D_41fe8. zstep F_41fec D_41fec. zstep F_41ff0 D_41ff0.
  stepn F_41ff4 D_41ff4.
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_miss_b_fn : forall regs (M rom : word -> option byte) (pcp n al ca ia : Z),
  getr regs 10 = Z_to_bv 64 1 -> getr regs 9 = Z_to_bv 64 pcp -> getr regs 18 = Z_to_bv 64 al -> getr regs 19 = Z_to_bv 64 ca -> getr regs 20 = Z_to_bv 64 ia ->
  0 <= pcp -> pcp + 80 < 2 ^ 64 -> 1 <= n < 2 ^ 31 -> cellA M pcp 4 n ->
  msteps ASEGS (mkst regs (0x41ff8 : word) M rom) (mkst (regupd (regupd (regupd (regupd regs 10 (Z_to_bv 64 ia)) 11 (Z_to_bv 64 ca)) 12 (Z_to_bv 64 n)) 13 (Z_to_bv 64 al)) (0x41efc : word) M rom).
Proof.
  intros regs M rom pcp n al ca ia H10 H9 H18 H19 H20 Hp Hp' Hn Cn.
  zbft F_41ff8 D_41ff8.
  zlw F_41ffc D_41ffc pcp Cn.
  zstep F_42000 D_42000. zstep F_42004 D_42004. zstep F_42008 D_42008.
  stepn F_4200c D_4200c.
  zret.
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Lemma art_cache_pop50 : forall regs (M rom : word -> option byte) (c ca ia cnt csz ch st spb : Z),
  getr regs 8 = Z_to_bv 64 c -> getr regs 9 = Z_to_bv 64 (ca + 80 * c) -> getr regs 11 = Z_to_bv 64 ca -> getr regs 10 = Z_to_bv 64 ia -> getr regs 12 = Z_to_bv 64 cnt ->
  1 <= c <= 31 -> 0 <= ca -> ca + 4096 < 2 ^ 64 -> ca mod 8 = 0 -> 0 <= ia -> ia + 4096 < 2 ^ 64 ->
  1 <= cnt <= 16 -> 0 <= csz < 2 ^ 64 -> 0 <= ch < 2 ^ 32 -> 0 <= st < 2 ^ 64 -> 0 <= spb < 2 ^ 64 ->
  cellA M (ca + 80 * c + 8) 8 csz -> cellA M (ca + 80 * c + 16 + 4 * (cnt - 1)) 4 ch ->
  cellA M (ca + 2576) 8 st -> cellA M (ia + 32) 8 spb ->
  wokA M (ca + 80 * c) 4 -> wokA M (ca + 2576) 8 ->
  apart (ca + 80 * c) 4 (ia + 32) 8 -> apart (ca + 2576) 8 (ia + 32) 8 ->
  exists regs',
    msteps ASEGS (mkst regs (0x41efc : word) M rom)
                 (mkst regs' (0x41f38 : word) (Wn 8 (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 2576) (st + csz)) rom)
    /\ getr regs' 10 = Z_to_bv 64 (spb + c * 2 ^ 32 + ch * 16)
    /\ (forall r : reg, r <> 8%bv -> r <> 9%bv -> r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 14%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom c ca ia cnt csz ch st spb H8 H9 H11 H10 H12 Hc Hca Hca' Hca8 Hia Hia' Hcnt Hcsz Hch Hst Hspb
         Ccsz Cch Cst Cspb Wcnt Wst Ap1 Ap2.
  eexists. split.
  - zstep F_41efc D_41efc.
    zstep F_41f00 D_41f00.
    zstep F_41f04 D_41f04.
    zsw F_41f08 D_41f08 (ca + 80 * c) (cnt - 1) ltac:(exact Wcnt).
    zstep F_41f0c D_41f0c.
    assert (Ccsz1 : cellA (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 80 * c + 8) 8 csz) by recell Ccsz.
    assert (Cch1 : cellA (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 80 * c + 16 + 4 * (cnt - 1)) 4 ch) by recell Cch.
    assert (Cst1 : cellA (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 2576) 8 st) by recell Cst.
    assert (Wst1 : wokA (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 2576) 8) by rewok Wst.
    zld F_41f10 D_41f10 (ca + 80 * c + 8) Ccsz1.
    stepn F_41f14 D_41f14. rewrite (art_zb_srli_exact _ 30 (4 * (cnt - 1))) by lia.
    zstep F_41f18 D_41f18.
    zlwu F_41f1c D_41f1c (ca + 80 * c + 16 + 4 * (cnt - 1)) Cch1.
    zamoadd_d F_41f20 D_41f20 (ca + 2576) st csz Cst1 ltac:(exact Wst1).
    assert (Cspb2 : cellA (Wn 8 (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 2576) (st + csz)) (ia + 32) 8 spb) by recell Cspb.
    zld F_41f24 D_41f24 (ia + 32) Cspb2.
    zstep F_41f28 D_41f28.
    zstep F_41f2c D_41f2c.
    zstep F_41f30 D_41f30.
    zstep F_41f34 D_41f34.
    apply mst_refl.
  - split; [gres; f_equal; lia|].
    intros r N8 N9 N10 N11 N12 N14; gres; try reflexivity; repeat (rewrite getr_other by (assumption || (symmetry; assumption) || reg_neq_tac)); reflexivity.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
End FPX.
