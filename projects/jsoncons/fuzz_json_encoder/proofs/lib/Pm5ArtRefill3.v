(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac Pm5ArtLeaf Pm5ArtAllocG Pm5ArtCachePop Pm5ArtCombAlloc Pm5ArtCombAllocHit Pm5ArtClassId Pm5ArtFree1 Pm5ArtRefill1 Pm5ArtRefill2.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import Pm5_code_5f000_60000.
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
  32 <= sp -> sp < 2 ^ 64 -> 0x6c4000 + 32 <= sp -> 4096 <= ca -> ca + 4096 < 2 ^ 64 -> 1 <= c <= 31 -> 0 <= ia < 2 ^ 64 -> 2 <= mc <= 16 ->
  apart (sp - 32) 32 ca 4096 ->
  wrA M (sp - 32) 32 -> cellA M (ca + 80 * c + 4) 4 mc ->
  msteps ASEGS (mkst regs (0x5ffa0 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x5ffe0 : bv 64)%bv) 2 (Z_to_bv 64 (sp - 32))) 8 (Z_to_bv 64 (ca + 80 * c))) 9 (Z_to_bv 64 (mc / 2))) 10 (Z_to_bv 64 ia)) 11 (Z_to_bv 64 (ca + 2560))) 12 (Z_to_bv 64 c)) 13 (Z_to_bv 64 (ca + 80 * c + 16))) 14 (Z_to_bv 64 (mc / 2)))
          (0x600a0 : word) (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) rom).
Proof.
  intros regs M rom raw sp ca c ia mc H1 H2 H10 H11 H12 H13 Hsp Hsp' IMG Hca Hca' Hc Hia Hmc A W Cmc.
  zstep F_5ff58 D_5ff58.
  zsd F_5ff5c D_5ff5c (sp - 8) (U raw) ltac:(rewok W). zsd F_5ff60 D_5ff60 (sp - 16) (U (getr regs 8)) ltac:(rewok W). zsd F_5ff64 D_5ff64 (sp - 24) (U (getr regs 9)) ltac:(rewok W).
  zstep F_5ff68 D_5ff68. zstep F_5ff6c D_5ff6c.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cmc' : cellA X (ca + 80 * c + 4) 4 mc) by (unfold apart in A; zcell) end.
  zlw F_5ff70 D_5ff70 (ca + 80 * c + 4) Cmc'.
  zbft F_5ff74 D_5ff74.
  stepn F_5ff78 D_5ff78. rwH. rewrite art_srliw_small by lia. change (2 ^ 1) with 2.
  zstep F_5ff7c D_5ff7c. zstep F_5ff80 D_5ff80. zstep F_5ff84 D_5ff84. zstep F_5ff88 D_5ff88. zstep F_5ff8c D_5ff8c. zstep F_5ff90 D_5ff90.
  stepn F_5ff94 D_5ff94.
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_refill_b_fn : forall regs (M rom : word -> option byte) (raw : word) (sp pcp n g8 g9 : Z),
  getr regs 2 = Z_to_bv 64 (sp - 32) -> getr regs 8 = Z_to_bv 64 pcp -> getr regs 9 = Z_to_bv 64 n -> getr regs 10 = Z_to_bv 64 1 ->
  32 <= sp -> sp < 2 ^ 64 -> 4096 <= pcp -> pcp + 80 < 2 ^ 64 -> 0 <= n < 2 ^ 31 -> ret_ok raw -> 0 <= g8 < 2 ^ 64 -> 0 <= g9 < 2 ^ 64 -> apart (sp - 32) 32 pcp 80 ->
  wrA M pcp 4 -> cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 g8 -> cellA M (sp - 24) 8 g9 ->
  msteps ASEGS (mkst regs (0x5ffe0 : word) M rom) (mkst (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (Z_to_bv 64 g8)) 9 (Z_to_bv 64 g9)) raw (Wn 4 M pcp n) rom).
Proof.
  intros regs M rom raw sp pcp n g8 g9 H2 H8 H9 H10 Hsp Hsp' Hp Hp' Hn Hret Hg8 Hg9 A W C8 C16 C24.
  zbft F_5ff98 D_5ff98.
  zsw F_5ff9c D_5ff9c pcp n ltac:(rewok W).
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C8' : cellA X (sp - 8) 8 (U raw)) by (unfold apart in A; zcell); assert (C16' : cellA X (sp - 16) 8 g8) by (unfold apart in A; zcell);
                                                   assert (C24' : cellA X (sp - 24) 8 g9) by (unfold apart in A; zcell) end.
  zld F_5ffa0 D_5ffa0 (sp - 8) C8'. rewrite Z_to_bv_bv_unsigned.
  zld F_5ffa4 D_5ffa4 (sp - 16) C16'. zld F_5ffa8 D_5ffa8 (sp - 24) C24'.
  zstep F_5ffac D_5ffac.
  stepret F_5ffb0 D_5ffb0 raw ltac:(rwH; reflexivity).
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_miss_a_fn : forall regs (M rom : word -> option byte) (c ca ia al : Z),
  getr regs 8 = Z_to_bv 64 c -> getr regs 10 = Z_to_bv 64 ia -> getr regs 11 = Z_to_bv 64 ca -> getr regs 13 = Z_to_bv 64 al ->
  1 <= c <= 31 -> 0 <= ca -> ca + 4096 < 2 ^ 64 -> 0 <= ia < 2 ^ 64 -> 0 <= al < 2 ^ 64 ->
  cellA M (ca + 80 * c) 4 0 ->
  msteps ASEGS (mkst regs (0x5f9e4 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x5fb00 : bv 64)%bv) 9 (Z_to_bv 64 (ca + 80 * c))) 10 (Z_to_bv 64 ca)) 11 (Z_to_bv 64 (ca + 80 * c))) 12 (Z_to_bv 64 ia)) 13 (Z_to_bv 64 c)) 18 (Z_to_bv 64 al)) 19 (Z_to_bv 64 ca)) 20 (Z_to_bv 64 ia))
          (0x5ffa0 : word) M rom).
Proof.
  intros regs M rom c ca ia al H8 H10 H11 H13 Hc Hca Hca' Hia Hal Ccnt.
  zbft F_5f99c D_5f99c.
  zstep F_5f9a0 D_5f9a0.
  zbft F_5f9a4 D_5f9a4.
  zstep F_5f9a8 D_5f9a8. zstep F_5f9ac D_5f9ac. zstep F_5f9b0 D_5f9b0.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Ccnt' : cellA X (ca + c * 80) 4 0) by (replace (ca + c * 80) with (ca + 80 * c) by lia; exact Ccnt) end.
  zlw F_5f9b4 D_5f9b4 (ca + c * 80) Ccnt'.
  zbtk F_5f9b8 D_5f9b8.
  zstep F_5fa98 D_5fa98. zstep F_5fa9c D_5fa9c. zstep F_5faa0 D_5faa0. zstep F_5faa4 D_5faa4. zstep F_5faa8 D_5faa8. zstep F_5faac D_5faac. zstep F_5fab0 D_5fab0.
  stepn F_5fab4 D_5fab4.
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_miss_b_fn : forall regs (M rom : word -> option byte) (pcp n al ca ia : Z),
  getr regs 10 = Z_to_bv 64 1 -> getr regs 9 = Z_to_bv 64 pcp -> getr regs 18 = Z_to_bv 64 al -> getr regs 19 = Z_to_bv 64 ca -> getr regs 20 = Z_to_bv 64 ia ->
  0 <= pcp -> pcp + 80 < 2 ^ 64 -> 1 <= n < 2 ^ 31 -> cellA M pcp 4 n ->
  msteps ASEGS (mkst regs (0x5fb00 : word) M rom) (mkst (regupd (regupd (regupd (regupd regs 10 (Z_to_bv 64 ia)) 11 (Z_to_bv 64 ca)) 12 (Z_to_bv 64 n)) 13 (Z_to_bv 64 al)) (0x5fa04 : word) M rom).
Proof.
  intros regs M rom pcp n al ca ia H10 H9 H18 H19 H20 Hp Hp' Hn Cn.
  zbft F_5fab8 D_5fab8.
  zlw F_5fabc D_5fabc pcp Cn.
  zstep F_5fac0 D_5fac0. zstep F_5fac4 D_5fac4. zstep F_5fac8 D_5fac8.
  stepn F_5facc D_5facc.
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
    msteps ASEGS (mkst regs (0x5fa04 : word) M rom)
                 (mkst regs' (0x5fa40 : word) (Wn 8 (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 2576) (st + csz)) rom)
    /\ getr regs' 10 = Z_to_bv 64 (spb + c * 2 ^ 32 + ch * 16)
    /\ (forall r : reg, r <> 8%bv -> r <> 9%bv -> r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 14%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom c ca ia cnt csz ch st spb H8 H9 H11 H10 H12 Hc Hca Hca' Hca8 Hia Hia' Hcnt Hcsz Hch Hst Hspb
         Ccsz Cch Cst Cspb Wcnt Wst Ap1 Ap2.
  eexists. split.
  - zstep F_5f9bc D_5f9bc.
    zstep F_5f9c0 D_5f9c0.
    zstep F_5f9c4 D_5f9c4.
    zsw F_5f9c8 D_5f9c8 (ca + 80 * c) (cnt - 1) ltac:(exact Wcnt).
    zstep F_5f9cc D_5f9cc.
    assert (Ccsz1 : cellA (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 80 * c + 8) 8 csz) by recell Ccsz.
    assert (Cch1 : cellA (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 80 * c + 16 + 4 * (cnt - 1)) 4 ch) by recell Cch.
    assert (Cst1 : cellA (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 2576) 8 st) by recell Cst.
    assert (Wst1 : wokA (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 2576) 8) by rewok Wst.
    zld F_5f9d0 D_5f9d0 (ca + 80 * c + 8) Ccsz1.
    stepn F_5f9d4 D_5f9d4. rewrite (art_zb_srli_exact _ 30 (4 * (cnt - 1))) by lia.
    zstep F_5f9d8 D_5f9d8.
    zlwu F_5f9dc D_5f9dc (ca + 80 * c + 16 + 4 * (cnt - 1)) Cch1.
    zamoadd_d F_5f9e0 D_5f9e0 (ca + 2576) st csz Cst1 ltac:(exact Wst1).
    assert (Cspb2 : cellA (Wn 8 (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 2576) (st + csz)) (ia + 32) 8 spb) by recell Cspb.
    zld F_5f9e4 D_5f9e4 (ia + 32) Cspb2.
    zstep F_5f9e8 D_5f9e8.
    zstep F_5f9ec D_5f9ec.
    zstep F_5f9f0 D_5f9f0.
    zstep F_5f9f4 D_5f9f4.
    apply mst_refl.
  - split; [gres; f_equal; lia|].
    intros r N8 N9 N10 N11 N12 N14; gres; try reflexivity; repeat (rewrite getr_other by (assumption || (symmetry; assumption) || reg_neq_tac)); reflexivity.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
End FPX.
