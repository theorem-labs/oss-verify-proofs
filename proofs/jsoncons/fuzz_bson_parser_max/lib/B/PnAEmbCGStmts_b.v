(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmStatics PmStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgV8 PnModel. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnSpecsAX_b PnSpecsAa_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PNAECGS.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Section Mid.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (HI : asan_iface).
Variables (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit)
          (v b k : Z) (stk : list PNM.bstate) (sp r p1 p2 p3 m q : Z).

Definition SZ : Z := 40 * 2 ^ k.

(* [comment removed for export] *)
Definition gmid (B : Z) (R6 : bvmap 5 word) (M6 : word -> option byte) (model6 : Model) (Aw6 : list (Z * Z)) : Prop :=
  (* [comment removed for export] *)
  getr R6 (reg 2) = Z_to_bv 64 (sp - 192) /\ getr R6 (reg 8) = Z_to_bv 64 (sp - 104) /\ getr R6 (reg 9) = Z_to_bv 64 v
  /\ getr R6 (reg 18) = Z_to_bv 64 (v + 8) /\ getr R6 (reg 19) = Z_to_bv 64 (sp - 96) /\ getr R6 (reg 20) = Z_to_bv 64 B
  /\ getr R6 (reg 21) = Z_to_bv 64 2147450880
  /\ getr R6 (reg 22) = Z_to_bv 64 ((v + 8) / 8 + 2147450880) /\ getr R6 (reg 23) = Z_to_bv 64 ((sp - 96) / 8 + 2147450880) /\ getr R6 (reg 24) = Z_to_bv 64 (v / 8 + 2147450880)
  /\ (forall x, In x [3; 4; 25; 26; 27]%nat -> getr R6 (reg x) = getr R (reg x))
  (* [comment removed for export] *)
  /\ L5.u64_at RSEGS M6 (sp - 8) (bv_unsigned (getr R (reg 1))) /\ L5.u64_at RSEGS M6 (sp - 16) (bv_unsigned (getr R (reg 8)))
  /\ L5.u64_at RSEGS M6 (sp - 24) (bv_unsigned (getr R (reg 9))) /\ L5.u64_at RSEGS M6 (sp - 32) (bv_unsigned (getr R (reg 18)))
  /\ L5.u64_at RSEGS M6 (sp - 40) (bv_unsigned (getr R (reg 19))) /\ L5.u64_at RSEGS M6 (sp - 48) (bv_unsigned (getr R (reg 20)))
  /\ L5.u64_at RSEGS M6 (sp - 56) (bv_unsigned (getr R (reg 21))) /\ L5.u64_at RSEGS M6 (sp - 64) (bv_unsigned (getr R (reg 22)))
  /\ L5.u64_at RSEGS M6 (sp - 184) (bv_unsigned (getr R (reg 23))) /\ L5.u64_at RSEGS M6 (sp - 192) (bv_unsigned (getr R (reg 24)))
  /\ L5.u64_at RSEGS M6 (sp - 120) 731412 /\ L5.u64_at RSEGS M6 (sp - 128) (v + 8) /\ L5.u64_at RSEGS M6 (sp - 136) v
  /\ L5.u64_at RSEGS M6 (sp - 144) p3 /\ L5.u64_at RSEGS M6 (sp - 152) p2 /\ L5.u64_at RSEGS M6 (sp - 160) p1
  /\ L5.u64_at RSEGS M6 (sp - 168) ((v + 8) / 8 + 2147450880) /\ L5.u64_at RSEGS M6 (sp - 176) 2147450880 /\ L5.u64_at RSEGS M6 (sp - 104) B
  /\ L5.u64_at RSEGS M6 (sp - 96) (B + SZ) /\ L5.u64_at RSEGS M6 (sp - 88) (B + (SZ + 40)) /\ L5.u64_at RSEGS M6 (sp - 80) (B + 2 * SZ) /\ L5.u64_at RSEGS M6 (sp - 72) v
  (* [comment removed for export] *)
  /\ L5.u64_at RSEGS M6 v b /\ L5.u64_at RSEGS M6 (v + 8) (b + SZ) /\ L5.u64_at RSEGS M6 (v + 16) (b + SZ) /\ PMSPA.accA M6 v 24
  (* [comment removed for export] *)
  /\ 4096 <= B /\ B + 2 * SZ <= ahl_ceil ar /\ B mod 16 = 0 /\ app_mem B (2 * SZ) /\ (B + 2 * SZ <= 65536 \/ 0x696000 <= B)
  /\ (B + 2 * SZ <= b \/ b + SZ <= B) /\ (v + 24 <= B \/ B + 2 * SZ <= v)
  /\ L5.defined M6 B (2 * SZ) /\ shadow_zero M6 B (2 * SZ / 8)
  /\ (forall i, (i < length stk)%nat -> PNM.bstate_at RSEGS M6 (B + 40 * Z.of_nat i) (nth i stk PNM.bs_root))
  /\ (exists lenv, 0 <= lenv < 2 ^ 64 /\ PNM.bstate_at RSEGS M6 (B + SZ) (PNM.BS m lenv q 0 0))
  (* [comment removed for export] *)
  /\ ri_inv HI ((B, 2 * SZ) :: PNM.bvec_own b k ++ LBX) FF LK (adebit L cr (2 * SZ)) Aw6 M6 (vml_of model6) /\ L5CA.amodel_ok Aw6 model6
  /\ model_rt model model6 /\ incl Aw Aw6 /\ L5CA.astk ar M6 sp 12288 /\ shadow_zero M6 (sp - 12288) 1536
  /\ PMSTA.base_okA RSEGS PMA.AD M6
  /\ (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LBX FF 0 0 a -> ~ (sp - 12288 <= a < sp) -> ~ (v <= a < v + 24) -> M6 (Z_to_bv 64 a) = M (Z_to_bv 64 a))
  /\ (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LBX FF 0 0 a -> M (Z_to_bv 64 a) <> None -> M6 (Z_to_bv 64 a) <> None).
End Mid.
End PNAECGS.
Module PNAECH.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma stack_zeros12 M sp : shadow_zero M (sp - 12288) 1536 -> sp mod 16 = 0 -> L5KA.zeros_at M (sp / 8 + 2147450368) 512.
Proof.
  intros SZ S16 i Hi. pose proof (SZ (1024 + i) ltac:(Lia.lia)) as X. unfold byte_at, S, SB in X.
  replace (sp / 8 + 2147450368 + i) with ((sp - 12288) / 8 + 2147450880 + (1024 + i)) by Lia.lia. exact X.
Qed.
Lemma zsh1 M p : byte_at M (S p) 0 -> L5KA.zeros_at M (p / 8 + 2147450880) 1.
Proof. intros X i Hi. replace i with 0 by Lia.lia. rewrite Z.add_0_r. unfold byte_at, S, SB in X. exact X. Qed.
Lemma shadow_low b c j : 0 <= b -> b + c <= 2 ^ 47 -> 0 <= j < c / 8 -> 2147450880 <= S b + j < 2147450880 + 2 ^ 44.
Proof. unfold S, SB. intros. Lia.lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma vis_u8 H M1 M1v a v : mrestrict H M1 = M1v -> L5A.avis H a 1 -> 0 <= a -> a < 2 ^ 63 -> L5.u8_at RSEGS M1v a v -> L5.u8_at RSEGS M1 a v.
Proof. intros E AV H0 H1 X. rewrite <- E in X. exact (proj1 (L5A.u8_at_vis H M1 a v AV ltac:(Lia.lia) ltac:(Lia.lia)) X). Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma S_range x : 0 <= x < 2 ^ 47 -> 2147450880 <= S x < 2147450880 + 2 ^ 44.
Proof. unfold S, SB. intros. Lia.lia. Qed.
Lemma S_add8 a j : S a + j = S (a + 8 * j).
Proof. unfold S. Lia.lia. Qed.
Lemma stk_sh_idx sp i : sp mod 16 = 0 -> 0 <= i < 512 -> sp / 8 + 2147450368 + i = S (sp - 4096 + 8 * i).
Proof. unfold S, SB. intros. Lia.lia. Qed.
Lemma d32 x : (32 * x) / 8 = 4 * x.
Proof. Lia.lia. Qed.
Lemma d32b x : (32 * x + 32) / 8 = 4 * x + 4.
Proof. Lia.lia. Qed.
Lemma pow2k k : 0 <= k <= 11 -> 1 <= 2 ^ k <= 2048.
Proof. intros Hk. split; [pose proof (Z.pow_pos_nonneg 2 k ltac:(Lia.lia) ltac:(Lia.lia)); Lia.lia|]. change 2048 with (2 ^ 11). apply Z.pow_le_mono_r; Lia.lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
End PNAECH.
