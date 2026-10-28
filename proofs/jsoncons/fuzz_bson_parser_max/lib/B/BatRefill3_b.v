(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatAllocG_b BatCachePop_b BatCombAlloc_b BatCombAllocHit_b BatClassId_b BatFree1_b BatRefill1_b BatRefill2_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r41498_42984_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
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
#[using="Type"] Lemma art_refill_a_fn : forall regs (M rom : word -> option byte) (raw : word) (sp ca c ia mc : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 ca -> getr regs 11 = Z_to_bv 64 (ca + 80 * c) -> getr regs 12 = Z_to_bv 64 ia -> getr regs 13 = Z_to_bv 64 c ->
  32 <= sp -> sp < 2 ^ 64 -> 0x696000 + 32 <= sp -> 4096 <= ca -> ca + 4096 < 2 ^ 64 -> 1 <= c <= 31 -> 0 <= ia < 2 ^ 64 -> 2 <= mc <= 16 ->
  apart (sp - 32) 32 ca 4096 ->
  wrA M (sp - 32) 32 -> cellA M (ca + 80 * c + 4) 4 mc ->
  msteps ASEGS (mkst regs (0x5748c : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x574cc : bv 64)%bv) 2 (Z_to_bv 64 (sp - 32))) 8 (Z_to_bv 64 (ca + 80 * c))) 9 (Z_to_bv 64 (mc / 2))) 10 (Z_to_bv 64 ia)) 11 (Z_to_bv 64 (ca + 2560))) 12 (Z_to_bv 64 c)) 13 (Z_to_bv 64 (ca + 80 * c + 16))) 14 (Z_to_bv 64 (mc / 2)))
          (0x5758c : word) (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) rom).
Proof.
  intros regs M rom raw sp ca c ia mc H1 H2 H10 H11 H12 H13 Hsp Hsp' IMG Hca Hca' Hc Hia Hmc A W Cmc.
  zstep F_57074 D_57074.
  zsd F_57078 D_57078 (sp - 8) (U raw) ltac:(rewok W). zsd F_5707c D_5707c (sp - 16) (U (getr regs 8)) ltac:(rewok W). zsd F_57080 D_57080 (sp - 24) (U (getr regs 9)) ltac:(rewok W).
  zstep F_57084 D_57084. zstep F_57088 D_57088.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cmc' : cellA X (ca + 80 * c + 4) 4 mc) by (unfold apart in A; zcell) end.
  zlw F_5708c D_5708c (ca + 80 * c + 4) Cmc'.
  zbft F_57090 D_57090.
  stepn F_57094 D_57094. rwH. rewrite art_srliw_small by lia. change (2 ^ 1) with 2.
  zstep F_57098 D_57098. zstep F_5709c D_5709c. zstep F_570a0 D_570a0. zstep F_570a4 D_570a4. zstep F_570a8 D_570a8. zstep F_570ac D_570ac.
  stepn F_570b0 D_570b0.
  zret.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_refill_b_fn : forall regs (M rom : word -> option byte) (raw : word) (sp pcp n g8 g9 : Z),
  getr regs 2 = Z_to_bv 64 (sp - 32) -> getr regs 8 = Z_to_bv 64 pcp -> getr regs 9 = Z_to_bv 64 n -> getr regs 10 = Z_to_bv 64 1 ->
  32 <= sp -> sp < 2 ^ 64 -> 4096 <= pcp -> pcp + 80 < 2 ^ 64 -> 0 <= n < 2 ^ 31 -> ret_ok raw -> 0 <= g8 < 2 ^ 64 -> 0 <= g9 < 2 ^ 64 -> apart (sp - 32) 32 pcp 80 ->
  wrA M pcp 4 -> cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 g8 -> cellA M (sp - 24) 8 g9 ->
  msteps ASEGS (mkst regs (0x574cc : word) M rom) (mkst (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (Z_to_bv 64 g8)) 9 (Z_to_bv 64 g9)) raw (Wn 4 M pcp n) rom).
Proof.
  intros regs M rom raw sp pcp n g8 g9 H2 H8 H9 H10 Hsp Hsp' Hp Hp' Hn Hret Hg8 Hg9 A W C8 C16 C24.
  zbft F_570b4 D_570b4.
  zsw F_570b8 D_570b8 pcp n ltac:(rewok W).
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C8' : cellA X (sp - 8) 8 (U raw)) by (unfold apart in A; zcell); assert (C16' : cellA X (sp - 16) 8 g8) by (unfold apart in A; zcell);
                                                   assert (C24' : cellA X (sp - 24) 8 g9) by (unfold apart in A; zcell) end.
  zld F_570bc D_570bc (sp - 8) C8'. rewrite Z_to_bv_bv_unsigned.
  zld F_570c0 D_570c0 (sp - 16) C16'. zld F_570c4 D_570c4 (sp - 24) C24'.
  zstep F_570c8 D_570c8.
  stepret F_570cc D_570cc raw ltac:(rwH; reflexivity).
  zret.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_miss_a_fn : forall regs (M rom : word -> option byte) (c ca ia al : Z),
  getr regs 8 = Z_to_bv 64 c -> getr regs 10 = Z_to_bv 64 ia -> getr regs 11 = Z_to_bv 64 ca -> getr regs 13 = Z_to_bv 64 al ->
  1 <= c <= 31 -> 0 <= ca -> ca + 4096 < 2 ^ 64 -> 0 <= ia < 2 ^ 64 -> 0 <= al < 2 ^ 64 ->
  cellA M (ca + 80 * c) 4 0 ->
  msteps ASEGS (mkst regs (0x56ed0 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x56fec : bv 64)%bv) 9 (Z_to_bv 64 (ca + 80 * c))) 10 (Z_to_bv 64 ca)) 11 (Z_to_bv 64 (ca + 80 * c))) 12 (Z_to_bv 64 ia)) 13 (Z_to_bv 64 c)) 18 (Z_to_bv 64 al)) 19 (Z_to_bv 64 ca)) 20 (Z_to_bv 64 ia))
          (0x5748c : word) M rom).
Proof.
  intros regs M rom c ca ia al H8 H10 H11 H13 Hc Hca Hca' Hia Hal Ccnt.
  zbft F_56ab8 D_56ab8.
  zstep F_56abc D_56abc.
  zbft F_56ac0 D_56ac0.
  zstep F_56ac4 D_56ac4. zstep F_56ac8 D_56ac8. zstep F_56acc D_56acc.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Ccnt' : cellA X (ca + c * 80) 4 0) by (replace (ca + c * 80) with (ca + 80 * c) by lia; exact Ccnt) end.
  zlw F_56ad0 D_56ad0 (ca + c * 80) Ccnt'.
  zbtk F_56ad4 D_56ad4.
  zstep F_56bb4 D_56bb4. zstep F_56bb8 D_56bb8. zstep F_56bbc D_56bbc. zstep F_56bc0 D_56bc0. zstep F_56bc4 D_56bc4. zstep F_56bc8 D_56bc8. zstep F_56bcc D_56bcc.
  stepn F_56bd0 D_56bd0.
  zret.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_miss_b_fn : forall regs (M rom : word -> option byte) (pcp n al ca ia : Z),
  getr regs 10 = Z_to_bv 64 1 -> getr regs 9 = Z_to_bv 64 pcp -> getr regs 18 = Z_to_bv 64 al -> getr regs 19 = Z_to_bv 64 ca -> getr regs 20 = Z_to_bv 64 ia ->
  0 <= pcp -> pcp + 80 < 2 ^ 64 -> 1 <= n < 2 ^ 31 -> cellA M pcp 4 n ->
  msteps ASEGS (mkst regs (0x56fec : word) M rom) (mkst (regupd (regupd (regupd (regupd regs 10 (Z_to_bv 64 ia)) 11 (Z_to_bv 64 ca)) 12 (Z_to_bv 64 n)) 13 (Z_to_bv 64 al)) (0x56ef0 : word) M rom).
Proof.
  intros regs M rom pcp n al ca ia H10 H9 H18 H19 H20 Hp Hp' Hn Cn.
  zbft F_56bd4 D_56bd4.
  zlw F_56bd8 D_56bd8 pcp Cn.
  zstep F_56bdc D_56bdc. zstep F_56be0 D_56be0. zstep F_56be4 D_56be4.
  stepn F_56be8 D_56be8.
  zret.
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
#[using="Type"] Lemma art_cache_pop50 : forall regs (M rom : word -> option byte) (c ca ia cnt csz ch st spb : Z),
  getr regs 8 = Z_to_bv 64 c -> getr regs 9 = Z_to_bv 64 (ca + 80 * c) -> getr regs 11 = Z_to_bv 64 ca -> getr regs 10 = Z_to_bv 64 ia -> getr regs 12 = Z_to_bv 64 cnt ->
  1 <= c <= 31 -> 0 <= ca -> ca + 4096 < 2 ^ 64 -> ca mod 8 = 0 -> 0 <= ia -> ia + 4096 < 2 ^ 64 ->
  1 <= cnt <= 16 -> 0 <= csz < 2 ^ 64 -> 0 <= ch < 2 ^ 32 -> 0 <= st < 2 ^ 64 -> 0 <= spb < 2 ^ 64 ->
  cellA M (ca + 80 * c + 8) 8 csz -> cellA M (ca + 80 * c + 16 + 4 * (cnt - 1)) 4 ch ->
  cellA M (ca + 2576) 8 st -> cellA M (ia + 32) 8 spb ->
  wokA M (ca + 80 * c) 4 -> wokA M (ca + 2576) 8 ->
  apart (ca + 80 * c) 4 (ia + 32) 8 -> apart (ca + 2576) 8 (ia + 32) 8 ->
  exists regs',
    msteps ASEGS (mkst regs (0x56ef0 : word) M rom)
                 (mkst regs' (0x56f2c : word) (Wn 8 (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 2576) (st + csz)) rom)
    /\ getr regs' 10 = Z_to_bv 64 (spb + c * 2 ^ 32 + ch * 16)
    /\ (forall r : reg, r <> 8%bv -> r <> 9%bv -> r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 14%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom c ca ia cnt csz ch st spb H8 H9 H11 H10 H12 Hc Hca Hca' Hca8 Hia Hia' Hcnt Hcsz Hch Hst Hspb
         Ccsz Cch Cst Cspb Wcnt Wst Ap1 Ap2.
  eexists. split.
  - zstep F_56ad8 D_56ad8.
    zstep F_56adc D_56adc.
    zstep F_56ae0 D_56ae0.
    zsw F_56ae4 D_56ae4 (ca + 80 * c) (cnt - 1) ltac:(exact Wcnt).
    zstep F_56ae8 D_56ae8.
    assert (Ccsz1 : cellA (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 80 * c + 8) 8 csz) by recell Ccsz.
    assert (Cch1 : cellA (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 80 * c + 16 + 4 * (cnt - 1)) 4 ch) by recell Cch.
    assert (Cst1 : cellA (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 2576) 8 st) by recell Cst.
    assert (Wst1 : wokA (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 2576) 8) by rewok Wst.
    zld F_56aec D_56aec (ca + 80 * c + 8) Ccsz1.
    stepn F_56af0 D_56af0. rewrite (art_zb_srli_exact _ 30 (4 * (cnt - 1))) by lia.
    zstep F_56af4 D_56af4.
    zlwu F_56af8 D_56af8 (ca + 80 * c + 16 + 4 * (cnt - 1)) Cch1.
    zamoadd_d F_56afc D_56afc (ca + 2576) st csz Cst1 ltac:(exact Wst1).
    assert (Cspb2 : cellA (Wn 8 (Wn 4 M (ca + 80 * c) (cnt - 1)) (ca + 2576) (st + csz)) (ia + 32) 8 spb) by recell Cspb.
    zld F_56b00 D_56b00 (ia + 32) Cspb2.
    zstep F_56b04 D_56b04.
    zstep F_56b08 D_56b08.
    zstep F_56b0c D_56b0c.
    zstep F_56b10 D_56b10.
    apply mst_refl.
  - split; [gres; f_equal; lia|].
    intros r N8 N9 N10 N11 N12 N14; gres; try reflexivity; repeat (rewrite getr_other by (assumption || (symmetry; assumption) || reg_neq_tac)); reflexivity.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
End FPX.
