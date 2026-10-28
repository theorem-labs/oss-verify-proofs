(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BigLinkZA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0PlanKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanPlanCore
     BigLinkBase. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import BigLinkGlue_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import L5Kn_u L5KnA_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.seg Require LibSegBs_bbaA_u LibSegBs_bbaAx_u LibSegBs_bbaRe_u LibSegBs_bbaRf_u LibSegBs_bbaRx_u LibSegBs_bbaRs_u LibSegBs_bbaG0_u LibSegBs_bbaG1_u LibSegBs_bbaG2_u LibSegBs_bbaG3_u LibSegBs_bbaG4_u LibSegBs_bbaG5_u LibSegBs_bbaG6_u LibSegBs_bbaG7_u LibSegBs_bbaG8_u LibSegBs_bbaG9_u LibSegBs_bbaG10_u LibSegBs_bbaH1_u LibSegBs_bbaH2_u LibSegBs_bbaT_u LibSegBs_bbaE_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNSBAP.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
  intros A Pz. rewrite (BG.word_of_unsigned (edenot E e) (z mod BL.MM) (L5KA.zpolyA_sound E Vz e z A Pz)).
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, BL.MM. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof. intros K Ha Hv ->. eapply L5K.u64_of_KWord8; eauto. Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof. intros K Ha Hv ->. eapply L5K.u32_of_KWord4; eauto. Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof. intros K Ha Hv Hr ->. eapply L5K.u8_of_KWord1; eauto. Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
  intros K Ha Hv -> -> ->. cbn [kentry_ok] in K. destruct K as (_ & _ & Rd).
  rewrite L5K.adenot_e, Ha in Rd. rewrite (BG.word_of_unsigned _ _ Hv) in Rd.
  pose proof (bv_unsigned_in_range 64 (edenot E e)) as Rg. rewrite Hv in Rg. change (bv_modulus 64) with (2 ^ 64) in Rg.
  unfold word_to_le_bytes in Rd. rewrite Z_to_bv_unsigned in Rd. unfold bv_wrap in Rd. change (bv_modulus 64) with (2 ^ 64) in Rd.
  rewrite (Z.mod_small v (2 ^ 64)) in Rd by (clear - Rg; lia). cbn [Z_to_le_bytes rdn] in Rd. unfold L5.u8_at.
  assert (E1 : (Z_to_bv 64 (a + off) + 1 = Z_to_bv 64 (a + off + 1))%bv).
  { apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    change (bv_unsigned (1 : bv 64)) with 1. apply Z.add_mod_idemp_l. clear; lia. }
  rewrite E1 in Rd.
  destruct (match M (Z_to_bv 64 (a + off)) with Some b0 => Some b0 | None => seg_rom RSEGS (Z_to_bv 64 (a + off)) end) as [x|] eqn:X; [|discriminate].
  destruct (match M (Z_to_bv 64 (a + off + 1)) with Some b0 => Some b0 | None => seg_rom RSEGS (Z_to_bv 64 (a + off + 1)) end) as [y|] eqn:Y; [|discriminate].
  injection Rd as Ex Ey. split.
  - cbn [rdn]. rewrite X. subst x. f_equal. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    rewrite Z.mod_mod by (clear; lia). reflexivity.
  - cbn [rdn]. rewrite Y. subst y. f_equal. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    rewrite Z.shiftr_div_pow2 by (clear; lia). change (2 ^ 8) with 256. rewrite Z.mod_mod by (clear; lia). reflexivity.
Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof. intros K Ha Hn ->. eapply L5K.defined_of_KUnk; eauto. Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof. intros K Ha Hv -> ->. eapply L5KA.u8_of_KWord1_mod; eauto. Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof. intros K Ha Hn ->. eapply L5KA.zeros_of_KZero; eauto. Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof. intros Ha Hm. pose proof (L5K.land_le_r a m Ha ltac:(lia)). lia. Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
  intros Ha Hb. split. apply Z.lor_nonneg; lia.
  destruct (Z.eq_dec a 0) as [->|Na]. rewrite Z.lor_0_l. lia. destruct (Z.eq_dec b 0) as [->|Nb]. rewrite Z.lor_0_r. lia.
  apply (Z.log2_lt_cancel). rewrite Z.log2_lor by lia.
  apply Z.max_lub_lt; apply Z.log2_lt_pow2; try lia; change (2 ^ Z.log2 256) with 256; lia.
Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof. intros Ha Hm. rewrite Z.land_comm. exact (proj2 (L5K.land_le_r m a Hm Ha)). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
  intros Ha. assert (E : forallb (fun i => let x := Z.of_nat i in (0 <=? (Z.land x 18446744073709551613 + 2) mod 2 ^ 64) && ((Z.land x 18446744073709551613 + 2) mod 2 ^ 64 <? 256)) (seq 0 256) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in E. specialize (E (Z.to_nat a) ltac:(apply in_seq; lia)). cbn zeta in E. rewrite Z2Nat.id in E by lia. apply andb_prop in E as [E1 E2]. lia.
Qed.
Local Ltac byte_go :=
  lazymatch goal with
  | |- 0 <= (Z.land _ 18446744073709551613 + 2) mod _ < 256 => apply setbit1_byte; lia
  | |- 0 <= Z.lor _ _ < 256 => apply lor_byte; byte_go
  | |- 0 <= Z.land _ _ < 256 => apply land_byte; [nonneg_tac | lia]
  | _ => zfacts; first [lia | rewrite !Z.mod_small by (rewrite ?Z.mod_small by lia; lia); lia]
  end.
Local Ltac byte_tac0 k := k; byte_go.
Tactic Notation "byte_tac" tactic(k) := byte_tac0 k.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac solve_modk k :=
  repeat match goal with |- context [(?x mod 18446744073709551616) / _] => rewrite (Z.mod_small x 18446744073709551616) by (k; zfacts; lia) end;
  first [ rewrite Z.mod_small; [ first [reflexivity | k; lia] | k; L5K.zrange_tac ]
        | symmetry; eapply (Z.mod_unique_pos _ _ (-1)); k; unfold BL.MM; lia
        | symmetry; eapply (Z.mod_unique_pos _ _ 1); k; unfold BL.MM; lia ].
(* [comment removed for export] *)
Local Ltac pvz_hg tac := lazymatch goal with |- ?G0 => let PG := fresh "PGoal" in set (PG := G0); tac; subst PG end.
Local Ltac pvz_fold B k := lazymatch B with | ?A2 /\ ?B2 => pvz_fold B2 ltac:(fun T2 => let T := fresh "pvzT" in pose (T := A2 /\ T2); k T) | _ => k B end.
Local Ltac pvz_linconj := lazymatch goal with |- ?A /\ ?B => pvz_fold B ltac:(fun T => change_no_check (A /\ T)) | _ => idtac end.
Local Ltac pvz_unfold ZA := lazymatch type of ZA with forall j, _ = ?f j => tryif is_var f then unfold f else idtac | _ => idtac end.
Tactic Notation "evalEk" constr(ZA) tactic(k) :=
  L5K.norm_expr; eapply L5KA.zpolyA_val; [ apply (L5K.zagree_all _ _ _ ZA) | cbn [L5KA.zpolyA]; pvz_unfold ZA; reflexivity | solve_modk k ].
Tactic Notation "evalEk'" constr(ZA) constr(AG) tactic(k) :=
  L5K.norm_expr; eapply L5KA.zpolyA_val;
  [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity] | cbn [L5KA.zpolyA]; pvz_unfold ZA; reflexivity | solve_modk k ].
(* [comment removed for export] *)
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
(* [comment removed for export] *)
Local Ltac exactA H :=
  first [ exact H
        | lazymatch goal with
          | |- L5.u64_at _ _ ?a _ => lazymatch type of H with L5.u64_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.u8_at _ _ ?a _ => lazymatch type of H with L5.u8_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.u32_at _ _ ?a _ => lazymatch type of H with L5.u32_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.writable _ _ ?a _ => lazymatch type of H with L5.writable _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.defined _ ?a _ => lazymatch type of H with L5.defined _ ?b _ => replace a with b by (clear; lia) end
          | |- L5KA.zeros_at _ ?a _ => lazymatch type of H with L5KA.zeros_at _ ?b _ => replace a with b by (clear; lia) end
          end; exact H ].
(* [comment removed for export] *)
Local Ltac den_tac := first [reflexivity | lia | idtac].
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac apc_norm :=
  repeat match goal with
  | |- context [APC.eadd ?a ?b] => let t := eval vm_compute in (APC.eadd a b) in change (APC.eadd a b) with t
  | |- context [APC.esub ?a ?b] => let t := eval vm_compute in (APC.esub a b) in change (APC.esub a b) with t
  | |- context [APC.escale ?c ?e] => let t := eval vm_compute in (APC.escale c e) in change (APC.escale c e) with t
  | |- context [APC.eaddz ?a ?z] => let t := eval vm_compute in (APC.eaddz a z) in change (APC.eaddz a z) with t
  end.
(* [comment removed for export] *)
Local Ltac zp_norm := repeat (match goal with |- context [(?a <=? ?b) && (?c <? ?d)] => let r := eval vm_compute in ((a <=? b) && (c <? d)) in change ((a <=? b) && (c <? d)) with r end);
  repeat (match goal with |- context [2 ^ ?s] => let r := eval vm_compute in (2 ^ s) in change (2 ^ s) with r end); lazy beta iota zeta.
Local Ltac zp_mods := repeat match goal with |- context [(?x mod 18446744073709551616) / _] => rewrite (Z.mod_small x 18446744073709551616) by (zfacts; lia) end.
Local Ltac slotP ZA :=
  first [ assumption | reflexivity
        | (etransitivity; [eassumption|]; symmetry; eapply word_of_zpoly; [apply (L5K.zagree_all _ _ _ ZA) | cbn [L5KA.zpolyA]; pvz_unfold ZA; zp_norm; f_equal; zp_mods; first [reflexivity | clear; zfacts; lia | zfacts; lia]]) ].
(* [comment removed for export] *)
Local Ltac wordP' ZA AG :=
  eapply word_of_zpoly; [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity]
                        | cbn [L5KA.zpolyA]; pvz_unfold ZA; zp_norm; f_equal; zp_mods; first [reflexivity | clear; zfacts; lia | zfacts; lia] ].
(* [comment removed for export] *)
Module PbbaA := LibSegBs_bbaA_u.
Definition KS_bbaA : list nat := Eval vm_compute in (BG.kept_list 64 PbbaA.regs0 PbbaA.regs_out0).
Lemma KS_bbaA_ok : BG.kept_ok 64 PbbaA.regs0 PbbaA.regs_out0 KS_bbaA = true. Proof. vm_compute. reflexivity. Qed.
Lemma bbaA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) ->
  140735332483168 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 -> 140735332483168 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 96) + 96 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 96)) -> 140735332483168 <= (V 34%nat) <= 140737488355320 -> aligned (V 34%nat) 8 ->
  (((V 2%nat) - 96) + 96 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 2%nat) - 96)) -> L5.img_clear M 65536 754672 -> L5.u64_at RSEGS M (V 34%nat) 726280 -> ((V 33%nat) + 416 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 33%nat)) ->
  L5.u64_at RSEGS M ((V 33%nat) + 392) (V 41%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 400) ((V 41%nat) + (V 42%nat)) -> 4096 <= (V 41%nat) <= 140737488314328 -> aligned (V 41%nat) 8 ->
  40 <= (V 42%nat) <= 41000 -> aligned (V 42%nat) 8 -> L5.u8_at RSEGS M ((V 33%nat) + 10) 0 -> L5.u32_at RSEGS M ((V 33%nat) + 312) 1024 ->
  1 <= bv_unsigned (sext 64 (mul_div Instr.M_MUL (low32 (alu64 Instr.ALU_SRL (Z_to_bv 64 (V 42%nat)) (Z_to_bv 64 3))) (low32 (Z_to_bv 64 18446744072850558157)))) <= 1024 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 96) <= bv_unsigned a < ((V 2%nat) - 96) + 96) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 96) <= i < ((V 2%nat) - 96) + 96) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38824 M) (st fx' R' 0x370d0 M')
        /\ (forall x, In x KS_bbaA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 231552
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 44)
        /\ getr R' (reg 12) = Z_to_bv 64 4
        /\ getr R' (reg 13) = Z_to_bv 64 18446744072850558157
        /\ getr R' (reg 18) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 4
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G10 G11 G12 pvzI7 K1 K2 pvzI8 K4 K5 pvzI9 K7 K8 K9 K10 K11 K12 K13 pvzI10 K15 pvzI11 K17 K18 K19 pvzI12.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV41l; move HV41l before pvzI5; pose proof (proj2 pvzI5) as HV41r; move HV41r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV42l; move HV42l before pvzI6; pose proof (proj2 pvzI6) as HV42r; move HV42r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K14l; move K14l before pvzI10; pose proof (proj2 pvzI10) as K14r; move K14r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K16l; move K16l before pvzI11; pose proof (proj2 pvzI11) as K16r; move K16r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K20l; move K20l before pvzI12; pose proof (proj2 pvzI12) as K20r; move K20r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 41%nat => vz_41 | 42%nat => vz_42 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 43%nat. }
  assert (HR: regs_ok E PbbaA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbbaA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbbaA.kn0).
  { unfold know_ok, PbbaA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K8; lia | clear - HV2l HV2r K0l K0r K5 K8; lia | clear - HV2l HV2r K0l K0r K5 K8; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K6l K6r K8 K11; lia | clear - HV34l HV34r K6l K6r K8 K11; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r) | clear - HV33l HV33r K3l K3r K5 K11; lia | clear - HV33l HV33r K3l K3r K5 K11; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r HV42l HV42r K16l K16r) | clear - HV33l HV33r K3l K3r K5 K11; lia | clear - HV33l HV33r K3l K3r K5 K11; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV42l HV42r K16l K16r) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5 K11; lia | clear - HV33l HV33r K3l K3r K5 K11; lia | byte_tac ltac:(clear) | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5 K11; lia | clear - HV33l HV33r K3l K3r K5 K11; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [cbn [edenot ev]; reflexivity | exact (conj K20l K20r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbbaA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbbaA.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 96) <= bv_unsigned a < (vz_2 - 96) + 96) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbbaA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K8 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbbaA.ps0) with 0x370d0 in Hms. change (SR.ps_regs PbbaA.ps0) with (map (fun i => (i, nth i PbbaA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbbaA.ps0) with PbbaA.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbbaA.regs0 PbbaA.regs_out0 64 KS_bbaA KS_bbaA_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbbaA.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbbaA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaA.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbbaA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaA.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbbaA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaA.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbbaA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaA.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbbaA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaA.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbbaA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaA.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbbaA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaA.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbbaA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaA.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbbaA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaA.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbbaA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbbaAx := LibSegBs_bbaAx_u.
Definition KS_bbaAx : list nat := Eval vm_compute in (BG.kept_list 64 PbbaAx.regs0 PbbaAx.regs_out0).
Lemma KS_bbaAx_ok : BG.kept_ok 64 PbbaAx.regs0 PbbaAx.regs_out0 KS_bbaAx = true. Proof. vm_compute. reflexivity. Qed.
Lemma bbaAx_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) ->
  140735332483168 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 -> 140735332483168 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 96) + 96 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 96)) -> 140735332483168 <= (V 34%nat) <= 140737488355320 -> aligned (V 34%nat) 8 ->
  (((V 2%nat) - 96) + 96 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 2%nat) - 96)) -> L5.img_clear M 65536 754672 -> L5.u64_at RSEGS M (V 34%nat) 726280 -> ((V 33%nat) + 416 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 33%nat)) ->
  L5.u64_at RSEGS M ((V 33%nat) + 392) (V 41%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 400) ((V 41%nat) + (V 42%nat)) -> 4096 <= (V 41%nat) <= 140737488314328 -> aligned (V 41%nat) 8 ->
  40 <= (V 42%nat) <= 41000 -> aligned (V 42%nat) 8 -> L5.u8_at RSEGS M ((V 33%nat) + 10) 0 -> L5.u32_at RSEGS M ((V 33%nat) + 312) 1024 ->
  1025 <= bv_unsigned (sext 64 (mul_div Instr.M_MUL (low32 (alu64 Instr.ALU_SRL (Z_to_bv 64 (V 42%nat)) (Z_to_bv 64 3))) (low32 (Z_to_bv 64 18446744072850558157)))) <= 1025 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 96) <= bv_unsigned a < ((V 2%nat) - 96) + 96) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 96) <= i < ((V 2%nat) - 96) + 96) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38824 M) (st fx' R' 0x36ee4 M')
        /\ (forall x, In x KS_bbaAx -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 231800
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 4
        /\ getr R' (reg 13) = Z_to_bv 64 18446744072850558157
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G10 G11 G12 pvzI7 K1 K2 pvzI8 K4 K5 pvzI9 K7 K8 K9 K10 K11 K12 K13 pvzI10 K15 pvzI11 K17 K18 K19 pvzI12.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV41l; move HV41l before pvzI5; pose proof (proj2 pvzI5) as HV41r; move HV41r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV42l; move HV42l before pvzI6; pose proof (proj2 pvzI6) as HV42r; move HV42r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K14l; move K14l before pvzI10; pose proof (proj2 pvzI10) as K14r; move K14r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K16l; move K16l before pvzI11; pose proof (proj2 pvzI11) as K16r; move K16r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K20l; move K20l before pvzI12; pose proof (proj2 pvzI12) as K20r; move K20r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 41%nat => vz_41 | 42%nat => vz_42 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 43%nat. }
  assert (HR: regs_ok E PbbaAx.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbbaAx.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbbaAx.kn0).
  { unfold know_ok, PbbaAx.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K8; lia | clear - HV2l HV2r K0l K0r K5 K8; lia | clear - HV2l HV2r K0l K0r K5 K8; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K6l K6r K8 K11; lia | clear - HV34l HV34r K6l K6r K8 K11; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r) | clear - HV33l HV33r K3l K3r K5 K11; lia | clear - HV33l HV33r K3l K3r K5 K11; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r HV42l HV42r K16l K16r) | clear - HV33l HV33r K3l K3r K5 K11; lia | clear - HV33l HV33r K3l K3r K5 K11; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV42l HV42r K16l K16r) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5 K11; lia | clear - HV33l HV33r K3l K3r K5 K11; lia | byte_tac ltac:(clear) | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5 K11; lia | clear - HV33l HV33r K3l K3r K5 K11; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [cbn [edenot ev]; reflexivity | exact (conj K20l K20r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbbaAx.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbbaAx.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 96) <= bv_unsigned a < (vz_2 - 96) + 96) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbbaAx.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K8 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbbaAx.ps0) with 0x36ee4 in Hms. change (SR.ps_regs PbbaAx.ps0) with (map (fun i => (i, nth i PbbaAx.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbbaAx.ps0) with PbbaAx.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbbaAx.regs0 PbbaAx.regs_out0 64 KS_bbaAx KS_bbaAx_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbbaAx.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbbaAx.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaAx.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbbaAx.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaAx.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbbaAx.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaAx.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbbaAx.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaAx.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbbaAx.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaAx.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbbaAx.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaAx.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbbaAx.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbbaRe := LibSegBs_bbaRe_u.
Definition KS_bbaRe : list nat := Eval vm_compute in (BG.kept_list 64 PbbaRe.regs0 PbbaRe.regs_out0).
Lemma KS_bbaRe_ok : BG.kept_ok 64 PbbaRe.regs0 PbbaRe.regs_out0 KS_bbaRe = true. Proof. vm_compute. reflexivity. Qed.
Lemma bbaRe_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 10) = Z_to_bv 64 (V 46%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 4 ->
  140735332483168 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 -> 0 <= (V 46%nat) <= 3 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 56) <= bv_unsigned a < ((V 2%nat) - 56) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 56) <= i < ((V 2%nat) - 56) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38880 M) (st fx' R' 0x36ee4 M')
        /\ (forall x, In x KS_bbaRe -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 231800
        /\ getr R' (reg 10) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G18 G19 pvzI6 K1 K2 pvzI7.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV46l; move HV46l before pvzI5; pose proof (proj2 pvzI5) as HV46r; move HV46r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_46 := V 46%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 46%nat => Z_to_bv 64 vz_46 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 46%nat => vz_46 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 47%nat. }
  assert (HR: regs_ok E PbbaRe.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbbaRe.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbbaRe.kn0).
  { unfold know_ok, PbbaRe.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbbaRe.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbbaRe.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 56) <= bv_unsigned a < (vz_2 - 56) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbbaRe.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbbaRe.ps0) with 0x36ee4 in Hms. change (SR.ps_regs PbbaRe.ps0) with (map (fun i => (i, nth i PbbaRe.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbbaRe.ps0) with PbbaRe.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbbaRe.regs0 PbbaRe.regs_out0 64 KS_bbaRe KS_bbaRe_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbbaRe.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbbaRe.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaRe.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbbaRe.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbbaRe.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbbaRe.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbbaRf := LibSegBs_bbaRf_u.
Definition KS_bbaRf : list nat := Eval vm_compute in (BG.kept_list 64 PbbaRf.regs0 PbbaRf.regs_out0).
Lemma KS_bbaRf_ok : BG.kept_ok 64 PbbaRf.regs0 PbbaRf.regs_out0 KS_bbaRf = true. Proof. vm_compute. reflexivity. Qed.
Lemma bbaRf_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 10) = Z_to_bv 64 4 -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 4 ->
  140735332483168 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 36%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 38%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 39%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 40%nat) ->
  140735332483168 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 -> (((V 2%nat) - 96) + 96 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 96)) -> L5.writable RSEGS M ((V 33%nat) + 8) 1 ->
  L5.writable RSEGS M ((V 33%nat) + 400) 8 -> 140735332483168 <= (V 34%nat) <= 140737488355320 -> aligned (V 34%nat) 8 -> (((V 2%nat) - 96) + 96 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 2%nat) - 96)) ->
  L5.img_clear M 65536 754672 -> L5.u64_at RSEGS M (V 34%nat) 726280 -> ((V 33%nat) + 416 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 33%nat)) -> L5.u8_at RSEGS M ((V 33%nat) + 10) 0 ->
  L5.u32_at RSEGS M ((V 33%nat) + 312) 1024 -> L5.u64_at RSEGS M ((V 33%nat) + 400) (V 45%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 408) ((V 45%nat) + (V 48%nat)) -> 4096 <= (V 45%nat) <= 140737488314328 ->
  aligned (V 45%nat) 8 -> 40 <= (V 48%nat) <= 81920 -> L5.writable RSEGS M (V 45%nat) 40 -> (((V 2%nat) - 96) + 96 <= (V 45%nat) \/ (V 45%nat) + 40 <= ((V 2%nat) - 96)) ->
  ((V 45%nat) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= (V 45%nat)) -> ((V 45%nat) + 40 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 45%nat)) -> ((V 45%nat) + 40 <= (V 35%nat) \/ (V 35%nat) + 16 <= (V 45%nat)) -> 140735332483168 <= (V 35%nat) <= 140737488355312 ->
  aligned (V 35%nat) 8 -> (((V 2%nat) - 96) + 96 <= (V 35%nat) \/ (V 35%nat) + 16 <= ((V 2%nat) - 96)) -> L5.u32_at RSEGS M (V 35%nat) (V 50%nat) -> 0 <= (V 50%nat) <= 0 ->
  ((V 33%nat) + 416 <= (V 35%nat) \/ (V 35%nat) + 16 <= (V 33%nat)) -> ((V 34%nat) + 8 <= (V 35%nat) \/ (V 35%nat) + 16 <= (V 34%nat)) -> L5.defined M ((V 2%nat) - 44) 4 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 96) <= bv_unsigned a < ((V 2%nat) - 96) + 96) -> ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 1) -> ~ (((V 33%nat) + 400) <= bv_unsigned a < ((V 33%nat) + 400) + 8) -> ~ (((V 45%nat) + 0) <= bv_unsigned a < ((V 45%nat) + 0) + 40) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 96) <= i < ((V 2%nat) - 96) + 96) -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 1) -> ~ (((V 33%nat) + 400) <= i < ((V 33%nat) + 400) + 8) -> ~ (((V 45%nat) + 0) <= i < ((V 45%nat) + 0) + 40) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38880 M) (st fx' R' 0x38960 M')
        /\ (forall x, In x KS_bbaRf -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 40
        /\ getr R' (reg 12) = Z_to_bv 64 4
        /\ getr R' (reg 13) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 216316
        /\ getr R' (reg 18) = Z_to_bv 64 (V 39%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 400) ((V 45%nat) + 40)
        /\ L5.u8_at RSEGS M' ((V 45%nat) + 24) 0
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 16) 4
        /\ L5.u32_at RSEGS M' (V 45%nat) 3
        /\ L5.u64_at RSEGS M' ((V 45%nat) + 32) 0
        /\ L5.u8_at RSEGS M' ((V 33%nat) + 8) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 39%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 40%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 G2 G8 G9 G10 G18 G19 pvzI13 K1 K2 K3 K4 K5 K6 K7 pvzI14 K9 K10 K11 K12 pvzI15 K14 K15 K16 K17 K18 K19 K20 K21 K22 pvzI16 K24 pvzI17 K26 K27 K28 K29 K30 pvzI18 K32 K33 K34 pvzI19 K36 K37 K38.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV37l; move HV37l before pvzI6; pose proof (proj2 pvzI6) as HV37r; move HV37r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV38l; move HV38l before pvzI7; pose proof (proj2 pvzI7) as HV38r; move HV38r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV39l; move HV39l before pvzI8; pose proof (proj2 pvzI8) as HV39r; move HV39r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV40l; move HV40l before pvzI9; pose proof (proj2 pvzI9) as HV40r; move HV40r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV45l; move HV45l before pvzI10; pose proof (proj2 pvzI10) as HV45r; move HV45r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV48l; move HV48l before pvzI11; pose proof (proj2 pvzI11) as HV48r; move HV48r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV50l; move HV50l before pvzI12; pose proof (proj2 pvzI12) as HV50r; move HV50r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K0l; move K0l before pvzI13; pose proof (proj2 pvzI13) as K0r; move K0r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K8l; move K8l before pvzI14; pose proof (proj2 pvzI14) as K8r; move K8r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K13l; move K13l before pvzI15; pose proof (proj2 pvzI15) as K13r; move K13r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K23l; move K23l before pvzI16; pose proof (proj2 pvzI16) as K23r; move K23r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K25l; move K25l before pvzI17; pose proof (proj2 pvzI17) as K25r; move K25r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K31l; move K31l before pvzI18; pose proof (proj2 pvzI18) as K31r; move K31r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K35l; move K35l before pvzI19; pose proof (proj2 pvzI19) as K35r; move K35r before pvzI19; clear pvzI19.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 45%nat => Z_to_bv 64 vz_45 | 48%nat => Z_to_bv 64 vz_48 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 45%nat => vz_45 | 48%nat => vz_48 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PbbaRf.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbbaRf.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbbaRf.kn0).
  { unfold know_ok, PbbaRf.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15 K27 K33) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15 K27 K33) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15 K27 K33) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K15 K27 K33; lia | clear - HV2l HV2r K0l K0r K10 K15 K27 K33; lia | clear - HV2l HV2r K0l K0r K10 K15 K27 K33; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15 K27 K33) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K0l K0r K10 K15 K27 K33; lia | clear - HV2l HV2r K0l K0r K10 K15 K27 K33; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15 K27 K33) | evalEk ZA ltac:(clear - HV37l HV37r) | clear - HV2l HV2r K0l K0r K10 K15 K27 K33; lia | clear - HV2l HV2r K0l K0r K10 K15 K27 K33; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15 K27 K33) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV2l HV2r K0l K0r K10 K15 K27 K33; lia | clear - HV2l HV2r K0l K0r K10 K15 K27 K33; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15 K27 K33) | evalEk ZA ltac:(clear - HV39l HV39r) | clear - HV2l HV2r K0l K0r K10 K15 K27 K33; lia | clear - HV2l HV2r K0l K0r K10 K15 K27 K33; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15 K27 K33) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K10 K15 K27 K33; lia | clear - HV2l HV2r K0l K0r K10 K15 K27 K33; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K10 K18 K28 K36) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K10 K18 K28 K36) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15 K27 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K10 K18 K28 K36) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K10 K18 K28 K36) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K8l K8r K10 K18 K28 K36; lia | clear - HV33l HV33r K8l K8r K10 K18 K28 K36; lia | clear - HV33l HV33r K8l K8r K10 K18 K28 K36; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K10 K18 K28 K36) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K8l K8r K10 K18 K28 K36; lia | clear - HV33l HV33r K8l K8r K10 K18 K28 K36; lia | clear - HV33l HV33r K8l K8r K10 K18 K28 K36; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K13l K13r K15 K18 K29 K37) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K13l K13r K15 K18 K29 K37) | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15 K27 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K13l K13r K15 K18 K29 K37) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K13l K13r K15 K18 K29 K37) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K13l K13r K15 K18 K29 K37; lia | clear - HV34l HV34r K13l K13r K15 K18 K29 K37; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K10 K18 K28 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K13l K13r K15 K18 K29 K37) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K10 K18 K28 K36) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K8l K8r K10 K18 K28 K36; lia | clear - HV33l HV33r K8l K8r K10 K18 K28 K36; lia | byte_tac ltac:(clear) | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K10 K18 K28 K36) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K8l K8r K10 K18 K28 K36; lia | clear - HV33l HV33r K8l K8r K10 K18 K28 K36; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K10 K18 K28 K36) | evalEk ZA ltac:(clear - HV45l HV45r K23l K23r K27 K28 K29 K30) | clear - HV33l HV33r K8l K8r K10 K18 K28 K36; lia | clear - HV33l HV33r K8l K8r K10 K18 K28 K36; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K10 K18 K28 K36) | evalEk ZA ltac:(clear - HV45l HV45r K23l K23r K27 K28 K29 K30 HV48l HV48r K25l K25r) | clear - HV33l HV33r K8l K8r K10 K18 K28 K36; lia | clear - HV33l HV33r K8l K8r K10 K18 K28 K36; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K23l K23r K27 K28 K29 K30) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV45l HV45r K23l K23r K27 K28 K29 K30) | clear; lia | exact K24]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV45l HV45r K23l K23r K27 K28 K29 K30) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K23l K23r K27 K28 K29 K30; lia | clear - HV45l HV45r K23l K23r K27 K28 K29 K30; lia | clear - HV45l HV45r K23l K23r K27 K28 K29 K30; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15 K27 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K23l K23r K27 K28 K29 K30) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K23l K23r K27 K28 K29 K30) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K10 K18 K28 K36) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K23l K23r K27 K28 K29 K30) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K13l K13r K15 K18 K29 K37) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K23l K23r K27 K28 K29 K30) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K30 K31l K31r K33 K36 K37) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K30 K31l K31r K33 K36 K37) | exact (conj K31l K31r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K30 K31l K31r K33 K36 K37) | clear; lia | exact K32]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15 K27 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K30 K31l K31r K33 K36 K37) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV35l HV35r K30 K31l K31r K33 K36 K37) | evalEk ZA ltac:(clear - HV50l HV50r K35l K35r) | clear - HV35l HV35r K30 K31l K31r K33 K36 K37; lia | clear - HV35l HV35r K30 K31l K31r K33 K36 K37; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K35l K35r) | exact (conj K35l K35r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K10 K18 K28 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K30 K31l K31r K33 K36 K37) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K13l K13r K15 K18 K29 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K30 K31l K31r K33 K36 K37) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K15 K27 K33) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K15 K27 K33; lia | clear - HV2l HV2r K0l K0r K10 K15 K27 K33; lia | clear - HV2l HV2r K0l K0r K10 K15 K27 K33; lia | exactA K38]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbbaRf.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbbaRf.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 96) <= bv_unsigned a < (vz_2 - 96) + 96) -> ~ ((vz_33 + 8) <= bv_unsigned a < (vz_33 + 8) + 1) -> ~ ((vz_33 + 400) <= bv_unsigned a < (vz_33 + 400) + 8) -> ~ ((vz_45 + 0) <= bv_unsigned a < (vz_45 + 0) + 40) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PbbaRf.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15 K27 K33) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K15 K27 K33 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K10 K18 K28 K36) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K8l K8r K10 K18 K28 K36 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K10 K18 K28 K36) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K8l K8r K10 K18 K28 K36 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV45l HV45r K23l K23r K27 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear - HV45l HV45r K23l K23r K27 K28 K29 K30 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbbaRf.ps0) with 0x38960 in Hms. change (SR.ps_regs PbbaRf.ps0) with (map (fun i => (i, nth i PbbaRf.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbbaRf.ps0) with PbbaRf.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbbaRf.regs0 PbbaRf.regs_out0 64 KS_bbaRf KS_bbaRf_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbbaRf.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbbaRf.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaRf.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbbaRf.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaRf.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbbaRf.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaRf.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbbaRf.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaRf.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbbaRf.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaRf.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbbaRf.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaRf.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbbaRf.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaRf.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbbaRf.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaRf.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbbaRf.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaRf.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbbaRf.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaRf.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbbaRf.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K10 K18 K28 K36) | evalEk' ZA Hag ltac:(clear - HV45l HV45r K23l K23r K27 K28 K29 K30) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV45l HV45r K23l K23r K27 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV45l HV45r K23l K23r K27 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV45l HV45r K23l K23r K27 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV45l HV45r K23l K23r K27 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K10 K18 K28 K36) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15 K27 K33) | evalEk' ZA Hag ltac:(clear - HV36l HV36r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15 K27 K33) | evalEk' ZA Hag ltac:(clear - HV37l HV37r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15 K27 K33) | evalEk' ZA Hag ltac:(clear - HV38l HV38r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15 K27 K33) | evalEk' ZA Hag ltac:(clear - HV39l HV39r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K15 K27 K33) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbbaRx := LibSegBs_bbaRx_u.
Definition KS_bbaRx : list nat := Eval vm_compute in (BG.kept_list 64 PbbaRx.regs0 PbbaRx.regs_out0).
Lemma KS_bbaRx_ok : BG.kept_ok 64 PbbaRx.regs0 PbbaRx.regs_out0 KS_bbaRx = true. Proof. vm_compute. reflexivity. Qed.
Lemma bbaRx_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 10) = Z_to_bv 64 4 -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 4 ->
  140735332483168 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 36%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 38%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 39%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 40%nat) ->
  140735332483168 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 -> (((V 2%nat) - 96) + 96 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 96)) -> L5.writable RSEGS M ((V 33%nat) + 8) 1 ->
  140735332483168 <= (V 34%nat) <= 140737488355320 -> aligned (V 34%nat) 8 -> (((V 2%nat) - 96) + 96 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 2%nat) - 96)) -> L5.img_clear M 65536 754672 ->
  L5.u64_at RSEGS M (V 34%nat) 726280 -> ((V 33%nat) + 416 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 33%nat)) -> L5.u8_at RSEGS M ((V 33%nat) + 10) 0 -> L5.u32_at RSEGS M ((V 33%nat) + 312) 1024 ->
  140735332483168 <= (V 35%nat) <= 140737488355312 -> aligned (V 35%nat) 8 -> (((V 2%nat) - 96) + 96 <= (V 35%nat) \/ (V 35%nat) + 16 <= ((V 2%nat) - 96)) -> L5.u32_at RSEGS M (V 35%nat) (V 50%nat) ->
  1 <= (V 50%nat) <= 64 -> ((V 33%nat) + 416 <= (V 35%nat) \/ (V 35%nat) + 16 <= (V 33%nat)) -> ((V 34%nat) + 8 <= (V 35%nat) \/ (V 35%nat) + 16 <= (V 34%nat)) -> L5.defined M ((V 2%nat) - 44) 4 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 96) <= bv_unsigned a < ((V 2%nat) - 96) + 96) -> ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 96) <= i < ((V 2%nat) - 96) + 96) -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38880 M) (st fx' R' 0x38960 M')
        /\ (forall x, In x KS_bbaRx -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 216316
        /\ getr R' (reg 18) = Z_to_bv 64 (V 39%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 40%nat)
        /\ L5.u8_at RSEGS M' ((V 33%nat) + 8) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 39%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 40%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 G2 G8 G9 G10 G18 G19 pvzI11 K1 K2 K3 K4 K5 K6 K7 pvzI12 K9 K10 K11 pvzI13 K13 K14 K15 K16 K17 K18 K19 pvzI14 K21 K22 K23 pvzI15 K25 K26 K27.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV37l; move HV37l before pvzI6; pose proof (proj2 pvzI6) as HV37r; move HV37r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV38l; move HV38l before pvzI7; pose proof (proj2 pvzI7) as HV38r; move HV38r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV39l; move HV39l before pvzI8; pose proof (proj2 pvzI8) as HV39r; move HV39r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV40l; move HV40l before pvzI9; pose proof (proj2 pvzI9) as HV40r; move HV40r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV50l; move HV50l before pvzI10; pose proof (proj2 pvzI10) as HV50r; move HV50r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K0l; move K0l before pvzI11; pose proof (proj2 pvzI11) as K0r; move K0r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K8l; move K8l before pvzI12; pose proof (proj2 pvzI12) as K8r; move K8r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K12l; move K12l before pvzI13; pose proof (proj2 pvzI13) as K12r; move K12r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K20l; move K20l before pvzI14; pose proof (proj2 pvzI14) as K20r; move K20r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K24l; move K24l before pvzI15; pose proof (proj2 pvzI15) as K24r; move K24r before pvzI15; clear pvzI15.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PbbaRx.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbbaRx.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbbaRx.kn0).
  { unfold know_ok, PbbaRx.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K14 K22) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K14 K22) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K14 K22) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K14 K22; lia | clear - HV2l HV2r K0l K0r K10 K14 K22; lia | clear - HV2l HV2r K0l K0r K10 K14 K22; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K14 K22) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K0l K0r K10 K14 K22; lia | clear - HV2l HV2r K0l K0r K10 K14 K22; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K14 K22) | evalEk ZA ltac:(clear - HV37l HV37r) | clear - HV2l HV2r K0l K0r K10 K14 K22; lia | clear - HV2l HV2r K0l K0r K10 K14 K22; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K14 K22) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV2l HV2r K0l K0r K10 K14 K22; lia | clear - HV2l HV2r K0l K0r K10 K14 K22; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K14 K22) | evalEk ZA ltac:(clear - HV39l HV39r) | clear - HV2l HV2r K0l K0r K10 K14 K22; lia | clear - HV2l HV2r K0l K0r K10 K14 K22; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K14 K22) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K10 K14 K22; lia | clear - HV2l HV2r K0l K0r K10 K14 K22; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K10 K17 K25) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K10 K17 K25) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K14 K22) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K10 K17 K25) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K10 K17 K25) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K8l K8r K10 K17 K25; lia | clear - HV33l HV33r K8l K8r K10 K17 K25; lia | clear - HV33l HV33r K8l K8r K10 K17 K25; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K17 K26) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K17 K26) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K14 K22) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K17 K26) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K17 K26) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K12l K12r K14 K17 K26; lia | clear - HV34l HV34r K12l K12r K14 K17 K26; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K10 K17 K25) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K17 K26) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K10 K17 K25) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K8l K8r K10 K17 K25; lia | clear - HV33l HV33r K8l K8r K10 K17 K25; lia | byte_tac ltac:(clear) | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K10 K17 K25) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K8l K8r K10 K17 K25; lia | clear - HV33l HV33r K8l K8r K10 K17 K25; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K20l K20r K22 K25 K26) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K20l K20r K22 K25 K26) | clear; lia | exact K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K14 K22) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K20l K20r K22 K25 K26) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV35l HV35r K20l K20r K22 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K24l K24r) | clear - HV35l HV35r K20l K20r K22 K25 K26; lia | clear - HV35l HV35r K20l K20r K22 K25 K26; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K24l K24r) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K10 K17 K25) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K20l K20r K22 K25 K26) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K17 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K20l K20r K22 K25 K26) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K14 K22) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K14 K22; lia | clear - HV2l HV2r K0l K0r K10 K14 K22; lia | clear - HV2l HV2r K0l K0r K10 K14 K22; lia | exactA K27]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbbaRx.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbbaRx.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 96) <= bv_unsigned a < (vz_2 - 96) + 96) -> ~ ((vz_33 + 8) <= bv_unsigned a < (vz_33 + 8) + 1) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PbbaRx.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K14 K22) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K14 K22 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K10 K17 K25) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K8l K8r K10 K17 K25 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbbaRx.ps0) with 0x38960 in Hms. change (SR.ps_regs PbbaRx.ps0) with (map (fun i => (i, nth i PbbaRx.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbbaRx.ps0) with PbbaRx.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbbaRx.regs0 PbbaRx.regs_out0 64 KS_bbaRx KS_bbaRx_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbbaRx.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbbaRx.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaRx.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbbaRx.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaRx.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbbaRx.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaRx.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbbaRx.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaRx.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbbaRx.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaRx.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbbaRx.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaRx.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbbaRx.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaRx.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbbaRx.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaRx.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbbaRx.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaRx.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbbaRx.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaRx.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbbaRx.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K10 K17 K25) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K14 K22) | evalEk' ZA Hag ltac:(clear - HV36l HV36r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K14 K22) | evalEk' ZA Hag ltac:(clear - HV37l HV37r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K14 K22) | evalEk' ZA Hag ltac:(clear - HV38l HV38r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K14 K22) | evalEk' ZA Hag ltac:(clear - HV39l HV39r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K14 K22) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbbaRs := LibSegBs_bbaRs_u.
Definition KS_bbaRs : list nat := Eval vm_compute in (BG.kept_list 64 PbbaRs.regs0 PbbaRs.regs_out0).
Lemma KS_bbaRs_ok : BG.kept_ok 64 PbbaRs.regs0 PbbaRs.regs_out0 KS_bbaRs = true. Proof. vm_compute. reflexivity. Qed.
Lemma bbaRs_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 10) = Z_to_bv 64 4 -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 4 ->
  140735332483168 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 36%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 38%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 39%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 40%nat) ->
  140735332483168 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 -> (((V 2%nat) - 96) + 96 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 96)) -> L5.writable RSEGS M ((V 33%nat) + 8) 1 ->
  140735332483168 <= (V 34%nat) <= 140737488355320 -> aligned (V 34%nat) 8 -> (((V 2%nat) - 96) + 96 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 2%nat) - 96)) -> L5.img_clear M 65536 754672 ->
  L5.u64_at RSEGS M (V 34%nat) 726280 -> ((V 33%nat) + 416 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 33%nat)) -> L5.u8_at RSEGS M ((V 33%nat) + 10) 0 -> L5.u32_at RSEGS M ((V 33%nat) + 312) 1024 ->
  L5.u64_at RSEGS M ((V 33%nat) + 400) (V 45%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 408) (V 45%nat) -> 140735332483168 <= (V 35%nat) <= 140737488355312 -> aligned (V 35%nat) 8 ->
  (((V 2%nat) - 96) + 96 <= (V 35%nat) \/ (V 35%nat) + 16 <= ((V 2%nat) - 96)) -> L5.u32_at RSEGS M (V 35%nat) (V 50%nat) -> 0 <= (V 50%nat) <= 0 -> ((V 33%nat) + 416 <= (V 35%nat) \/ (V 35%nat) + 16 <= (V 33%nat)) ->
  ((V 34%nat) + 8 <= (V 35%nat) \/ (V 35%nat) + 16 <= (V 34%nat)) -> L5.defined M ((V 2%nat) - 44) 4 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 96) <= bv_unsigned a < ((V 2%nat) - 96) + 96) -> ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 96) <= i < ((V 2%nat) - 96) + 96) -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38880 M) (st fx' R' 0x38918 M')
        /\ (forall x, In x KS_bbaRs -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 231596
        /\ getr R' (reg 10) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 3
        /\ getr R' (reg 13) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 216316
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 64) 3
        /\ L5.u8_at RSEGS M' ((V 33%nat) + 8) 1
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 60) (bv_unsigned (getr R' (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) 4
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 39%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 40%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 G2 G8 G9 G10 G18 G19 pvzI12 K1 K2 K3 K4 K5 K6 K7 pvzI13 K9 K10 K11 pvzI14 K13 K14 K15 K16 K17 K18 K19 K20 K21 pvzI15 K23 K24 K25 pvzI16 K27 K28 K29.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV37l; move HV37l before pvzI6; pose proof (proj2 pvzI6) as HV37r; move HV37r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV38l; move HV38l before pvzI7; pose proof (proj2 pvzI7) as HV38r; move HV38r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV39l; move HV39l before pvzI8; pose proof (proj2 pvzI8) as HV39r; move HV39r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV40l; move HV40l before pvzI9; pose proof (proj2 pvzI9) as HV40r; move HV40r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV45l; move HV45l before pvzI10; pose proof (proj2 pvzI10) as HV45r; move HV45r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV50l; move HV50l before pvzI11; pose proof (proj2 pvzI11) as HV50r; move HV50r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K0l; move K0l before pvzI12; pose proof (proj2 pvzI12) as K0r; move K0r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K8l; move K8l before pvzI13; pose proof (proj2 pvzI13) as K8r; move K8r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K12l; move K12l before pvzI14; pose proof (proj2 pvzI14) as K12r; move K12r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K22l; move K22l before pvzI15; pose proof (proj2 pvzI15) as K22r; move K22r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K26l; move K26l before pvzI16; pose proof (proj2 pvzI16) as K26r; move K26r before pvzI16; clear pvzI16.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 45%nat => Z_to_bv 64 vz_45 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 45%nat => vz_45 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PbbaRs.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbbaRs.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbbaRs.kn0).
  { unfold know_ok, PbbaRs.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K14 K24) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K14 K24) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K14 K24) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K14 K24; lia | clear - HV2l HV2r K0l K0r K10 K14 K24; lia | clear - HV2l HV2r K0l K0r K10 K14 K24; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K14 K24) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K0l K0r K10 K14 K24; lia | clear - HV2l HV2r K0l K0r K10 K14 K24; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K14 K24) | evalEk ZA ltac:(clear - HV37l HV37r) | clear - HV2l HV2r K0l K0r K10 K14 K24; lia | clear - HV2l HV2r K0l K0r K10 K14 K24; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K14 K24) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV2l HV2r K0l K0r K10 K14 K24; lia | clear - HV2l HV2r K0l K0r K10 K14 K24; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K14 K24) | evalEk ZA ltac:(clear - HV39l HV39r) | clear - HV2l HV2r K0l K0r K10 K14 K24; lia | clear - HV2l HV2r K0l K0r K10 K14 K24; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K14 K24) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K10 K14 K24; lia | clear - HV2l HV2r K0l K0r K10 K14 K24; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K10 K17 K27) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K10 K17 K27) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K14 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K10 K17 K27) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K10 K17 K27) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K8l K8r K10 K17 K27; lia | clear - HV33l HV33r K8l K8r K10 K17 K27; lia | clear - HV33l HV33r K8l K8r K10 K17 K27; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K17 K28) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K17 K28) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K14 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K17 K28) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K17 K28) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K12l K12r K14 K17 K28; lia | clear - HV34l HV34r K12l K12r K14 K17 K28; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K10 K17 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K17 K28) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K10 K17 K27) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K8l K8r K10 K17 K27; lia | clear - HV33l HV33r K8l K8r K10 K17 K27; lia | byte_tac ltac:(clear) | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K10 K17 K27) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K8l K8r K10 K17 K27; lia | clear - HV33l HV33r K8l K8r K10 K17 K27; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K10 K17 K27) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV33l HV33r K8l K8r K10 K17 K27; lia | clear - HV33l HV33r K8l K8r K10 K17 K27; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K10 K17 K27) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV33l HV33r K8l K8r K10 K17 K27; lia | clear - HV33l HV33r K8l K8r K10 K17 K27; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K22l K22r K24 K27 K28) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K22l K22r K24 K27 K28) | clear; lia | exact K23]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K14 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K22l K22r K24 K27 K28) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV35l HV35r K22l K22r K24 K27 K28) | evalEk ZA ltac:(clear - HV50l HV50r K26l K26r) | clear - HV35l HV35r K22l K22r K24 K27 K28; lia | clear - HV35l HV35r K22l K22r K24 K27 K28; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K26l K26r) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K10 K17 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K22l K22r K24 K27 K28) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K17 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K22l K22r K24 K27 K28) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K14 K24) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K14 K24; lia | clear - HV2l HV2r K0l K0r K10 K14 K24; lia | clear - HV2l HV2r K0l K0r K10 K14 K24; lia | exactA K29]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbbaRs.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbbaRs.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 96) <= bv_unsigned a < (vz_2 - 96) + 96) -> ~ ((vz_33 + 8) <= bv_unsigned a < (vz_33 + 8) + 1) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PbbaRs.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K14 K24) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K14 K24 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K10 K17 K27) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K8l K8r K10 K17 K27 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbbaRs.ps0) with 0x38918 in Hms. change (SR.ps_regs PbbaRs.ps0) with (map (fun i => (i, nth i PbbaRs.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbbaRs.ps0) with PbbaRs.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbbaRs.regs0 PbbaRs.regs_out0 64 KS_bbaRs KS_bbaRs_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbbaRs.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbbaRs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaRs.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbbaRs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaRs.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbbaRs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaRs.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbbaRs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaRs.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbbaRs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaRs.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbbaRs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K14 K24) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K10 K17 K27) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K14 K24) | rewrite (BG.out_reg PbbaRs.regs_out0 E' R' 19 Hregs) by (clear; lia); cbn [nth PbbaRs.regs_out0]; reflexivity | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K14 K24) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K14 K24) | evalEk' ZA Hag ltac:(clear - HV36l HV36r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K14 K24) | evalEk' ZA Hag ltac:(clear - HV37l HV37r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K14 K24) | evalEk' ZA Hag ltac:(clear - HV38l HV38r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K14 K24) | evalEk' ZA Hag ltac:(clear - HV39l HV39r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K14 K24) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbbaG0 := LibSegBs_bbaG0_u.
Definition KS_bbaG0 : list nat := Eval vm_compute in (BG.kept_list 64 PbbaG0.regs0 PbbaG0.regs_out0).
Lemma KS_bbaG0_ok : BG.kept_ok 64 PbbaG0.regs0 PbbaG0.regs_out0 KS_bbaG0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bbaG0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 19%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 (V 19%nat) ->
  140735332483184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 224) 224 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 36%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 38%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 39%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 40%nat) ->
  140735332483168 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 -> L5.img_clear M 65536 754672 -> L5.u64_at RSEGS M ((V 33%nat) + 392) (V 41%nat) ->
  L5.u64_at RSEGS M ((V 33%nat) + 400) ((V 41%nat) + 40) -> L5.u64_at RSEGS M ((V 33%nat) + 408) ((V 41%nat) + 40) -> 4096 <= (V 41%nat) <= 140737488314328 -> aligned (V 41%nat) 16 ->
  (((V 2%nat) - 224) + 224 <= (V 41%nat) \/ (V 41%nat) + 40 <= ((V 2%nat) - 224)) -> ((V 41%nat) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= (V 41%nat)) -> (((V 2%nat) - 224) + 224 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 224)) -> L5.u32_at RSEGS M ((V 2%nat) - 64) 3 ->
  L5.u32_at RSEGS M ((V 2%nat) - 60) (V 19%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) 4 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 224) <= bv_unsigned a < ((V 2%nat) - 224) + 224) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 224) <= i < ((V 2%nat) - 224) + 224) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38918 M) (st fx' R' 0xb03b8 M')
        /\ (forall x, In x KS_bbaG0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 223860
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 192)
        /\ getr R' (reg 8) = Z_to_bv 64 2
        /\ getr R' (reg 9) = Z_to_bv 64 1
        /\ getr R' (reg 10) = Z_to_bv 64 80
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 392)
        /\ getr R' (reg 14) = Z_to_bv 64 14757395258967641293
        /\ getr R' (reg 15) = Z_to_bv 64 461168601842738791
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 2%nat) - 60)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) ((V 2%nat) - 144)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) 223340
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) ((V 33%nat) + 392)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((V 2%nat) - 56)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) ((V 33%nat) + 392)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) 229952
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 19%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 231724
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 39%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 40%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 64) 3
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 60) (V 19%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 G2 G8 G9 G18 G19 pvzI12 K1 K2 K3 K4 K5 K6 K7 pvzI13 K9 K10 K11 K12 K13 pvzI14 K15 K16 K17 K18 K19 K20 K21.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV19l; move HV19l before pvzI2; pose proof (proj2 pvzI2) as HV19r; move HV19r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV35l; move HV35l before pvzI5; pose proof (proj2 pvzI5) as HV35r; move HV35r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV36l; move HV36l before pvzI6; pose proof (proj2 pvzI6) as HV36r; move HV36r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV37l; move HV37l before pvzI7; pose proof (proj2 pvzI7) as HV37r; move HV37r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV38l; move HV38l before pvzI8; pose proof (proj2 pvzI8) as HV38r; move HV38r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV39l; move HV39l before pvzI9; pose proof (proj2 pvzI9) as HV39r; move HV39r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV40l; move HV40l before pvzI10; pose proof (proj2 pvzI10) as HV40r; move HV40r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV41l; move HV41l before pvzI11; pose proof (proj2 pvzI11) as HV41r; move HV41r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K0l; move K0l before pvzI12; pose proof (proj2 pvzI12) as K0r; move K0r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K8l; move K8l before pvzI13; pose proof (proj2 pvzI13) as K8r; move K8r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K14l; move K14l before pvzI14; pose proof (proj2 pvzI14) as K14r; move K14r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_19 := V 19%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 19%nat => Z_to_bv 64 vz_19 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 19%nat => vz_19 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 41%nat => vz_41 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E PbbaG0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbbaG0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbbaG0.kn0).
  { unfold know_ok, PbbaG0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV37l HV37r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV39l HV39r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | clear - HV33l HV33r K8l K8r K17 K18; lia | clear - HV33l HV33r K8l K8r K17 K18; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | clear - HV33l HV33r K8l K8r K17 K18; lia | clear - HV33l HV33r K8l K8r K17 K18; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | clear - HV33l HV33r K8l K8r K17 K18; lia | clear - HV33l HV33r K8l K8r K17 K18; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV19l HV19r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K21]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbbaG0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbbaG0.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 224) <= bv_unsigned a < (vz_2 - 224) + 224) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbbaG0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K18 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbbaG0.ps0) with 0xb03b8 in Hms. change (SR.ps_regs PbbaG0.ps0) with (map (fun i => (i, nth i PbbaG0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbbaG0.ps0) with PbbaG0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbbaG0.regs0 PbbaG0.regs_out0 64 KS_bbaG0 KS_bbaG0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbbaG0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbbaG0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG0.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbbaG0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG0.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbbaG0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG0.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbbaG0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbbaG0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbbaG0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbbaG0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG0.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbbaG0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG0.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbbaG0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG0.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbbaG0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG0.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbbaG0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG0.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbbaG0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K17 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K17 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV19l HV19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV35l HV35r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K17 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV36l HV36r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV37l HV37r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV38l HV38r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV39l HV39r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV19l HV19r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbbaG1 := LibSegBs_bbaG1_u.
Definition KS_bbaG1 : list nat := Eval vm_compute in (BG.kept_list 64 PbbaG1.regs0 PbbaG1.regs_out0).
Lemma KS_bbaG1_ok : BG.kept_ok 64 PbbaG1.regs0 PbbaG1.regs_out0 KS_bbaG1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bbaG1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 19%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 (V 19%nat) ->
  140735332483184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 224) 224 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 36%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 38%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 39%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 40%nat) ->
  140735332483168 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 -> L5.img_clear M 65536 754672 -> L5.u64_at RSEGS M ((V 33%nat) + 392) (V 41%nat) ->
  L5.u64_at RSEGS M ((V 33%nat) + 400) ((V 41%nat) + 80) -> L5.u64_at RSEGS M ((V 33%nat) + 408) ((V 41%nat) + 80) -> 4096 <= (V 41%nat) <= 140737488314328 -> aligned (V 41%nat) 16 ->
  (((V 2%nat) - 224) + 224 <= (V 41%nat) \/ (V 41%nat) + 80 <= ((V 2%nat) - 224)) -> ((V 41%nat) + 80 <= (V 33%nat) \/ (V 33%nat) + 416 <= (V 41%nat)) -> (((V 2%nat) - 224) + 224 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 224)) -> L5.u32_at RSEGS M ((V 2%nat) - 64) 3 ->
  L5.u32_at RSEGS M ((V 2%nat) - 60) (V 19%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) 4 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 224) <= bv_unsigned a < ((V 2%nat) - 224) + 224) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 224) <= i < ((V 2%nat) - 224) + 224) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38918 M) (st fx' R' 0xb03b8 M')
        /\ (forall x, In x KS_bbaG1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 223860
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 192)
        /\ getr R' (reg 8) = Z_to_bv 64 4
        /\ getr R' (reg 9) = Z_to_bv 64 2
        /\ getr R' (reg 10) = Z_to_bv 64 160
        /\ getr R' (reg 11) = Z_to_bv 64 4
        /\ getr R' (reg 12) = Z_to_bv 64 2
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 392)
        /\ getr R' (reg 14) = Z_to_bv 64 14757395258967641293
        /\ getr R' (reg 15) = Z_to_bv 64 461168601842738791
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 2%nat) - 60)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) ((V 2%nat) - 144)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) 223340
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) ((V 33%nat) + 392)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((V 2%nat) - 56)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) ((V 33%nat) + 392)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) 229952
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 19%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 231724
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 39%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 40%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 64) 3
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 60) (V 19%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 G2 G8 G9 G18 G19 pvzI12 K1 K2 K3 K4 K5 K6 K7 pvzI13 K9 K10 K11 K12 K13 pvzI14 K15 K16 K17 K18 K19 K20 K21.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV19l; move HV19l before pvzI2; pose proof (proj2 pvzI2) as HV19r; move HV19r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV35l; move HV35l before pvzI5; pose proof (proj2 pvzI5) as HV35r; move HV35r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV36l; move HV36l before pvzI6; pose proof (proj2 pvzI6) as HV36r; move HV36r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV37l; move HV37l before pvzI7; pose proof (proj2 pvzI7) as HV37r; move HV37r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV38l; move HV38l before pvzI8; pose proof (proj2 pvzI8) as HV38r; move HV38r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV39l; move HV39l before pvzI9; pose proof (proj2 pvzI9) as HV39r; move HV39r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV40l; move HV40l before pvzI10; pose proof (proj2 pvzI10) as HV40r; move HV40r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV41l; move HV41l before pvzI11; pose proof (proj2 pvzI11) as HV41r; move HV41r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K0l; move K0l before pvzI12; pose proof (proj2 pvzI12) as K0r; move K0r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K8l; move K8l before pvzI13; pose proof (proj2 pvzI13) as K8r; move K8r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K14l; move K14l before pvzI14; pose proof (proj2 pvzI14) as K14r; move K14r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_19 := V 19%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 19%nat => Z_to_bv 64 vz_19 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 19%nat => vz_19 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 41%nat => vz_41 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E PbbaG1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbbaG1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbbaG1.kn0).
  { unfold know_ok, PbbaG1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV37l HV37r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV39l HV39r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | clear - HV33l HV33r K8l K8r K17 K18; lia | clear - HV33l HV33r K8l K8r K17 K18; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | clear - HV33l HV33r K8l K8r K17 K18; lia | clear - HV33l HV33r K8l K8r K17 K18; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | clear - HV33l HV33r K8l K8r K17 K18; lia | clear - HV33l HV33r K8l K8r K17 K18; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV19l HV19r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K21]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbbaG1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbbaG1.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 224) <= bv_unsigned a < (vz_2 - 224) + 224) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbbaG1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K18 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbbaG1.ps0) with 0xb03b8 in Hms. change (SR.ps_regs PbbaG1.ps0) with (map (fun i => (i, nth i PbbaG1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbbaG1.ps0) with PbbaG1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbbaG1.regs0 PbbaG1.regs_out0 64 KS_bbaG1 KS_bbaG1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbbaG1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbbaG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG1.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbbaG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG1.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbbaG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG1.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbbaG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbbaG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbbaG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbbaG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG1.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbbaG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG1.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbbaG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG1.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbbaG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG1.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbbaG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG1.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbbaG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K17 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K17 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV19l HV19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV35l HV35r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K17 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV36l HV36r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV37l HV37r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV38l HV38r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV39l HV39r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV19l HV19r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbbaG2 := LibSegBs_bbaG2_u.
Definition KS_bbaG2 : list nat := Eval vm_compute in (BG.kept_list 64 PbbaG2.regs0 PbbaG2.regs_out0).
Lemma KS_bbaG2_ok : BG.kept_ok 64 PbbaG2.regs0 PbbaG2.regs_out0 KS_bbaG2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bbaG2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 19%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 (V 19%nat) ->
  140735332483184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 224) 224 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 36%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 38%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 39%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 40%nat) ->
  140735332483168 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 -> L5.img_clear M 65536 754672 -> L5.u64_at RSEGS M ((V 33%nat) + 392) (V 41%nat) ->
  L5.u64_at RSEGS M ((V 33%nat) + 400) ((V 41%nat) + 160) -> L5.u64_at RSEGS M ((V 33%nat) + 408) ((V 41%nat) + 160) -> 4096 <= (V 41%nat) <= 140737488314328 -> aligned (V 41%nat) 16 ->
  (((V 2%nat) - 224) + 224 <= (V 41%nat) \/ (V 41%nat) + 160 <= ((V 2%nat) - 224)) -> ((V 41%nat) + 160 <= (V 33%nat) \/ (V 33%nat) + 416 <= (V 41%nat)) -> (((V 2%nat) - 224) + 224 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 224)) -> L5.u32_at RSEGS M ((V 2%nat) - 64) 3 ->
  L5.u32_at RSEGS M ((V 2%nat) - 60) (V 19%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) 4 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 224) <= bv_unsigned a < ((V 2%nat) - 224) + 224) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 224) <= i < ((V 2%nat) - 224) + 224) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38918 M) (st fx' R' 0xb03b8 M')
        /\ (forall x, In x KS_bbaG2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 223860
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 192)
        /\ getr R' (reg 8) = Z_to_bv 64 8
        /\ getr R' (reg 9) = Z_to_bv 64 4
        /\ getr R' (reg 10) = Z_to_bv 64 320
        /\ getr R' (reg 11) = Z_to_bv 64 8
        /\ getr R' (reg 12) = Z_to_bv 64 4
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 392)
        /\ getr R' (reg 14) = Z_to_bv 64 14757395258967641293
        /\ getr R' (reg 15) = Z_to_bv 64 461168601842738791
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 2%nat) - 60)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) ((V 2%nat) - 144)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) 223340
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) ((V 33%nat) + 392)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((V 2%nat) - 56)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) ((V 33%nat) + 392)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) 229952
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 19%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 231724
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 39%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 40%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 64) 3
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 60) (V 19%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 G2 G8 G9 G18 G19 pvzI12 K1 K2 K3 K4 K5 K6 K7 pvzI13 K9 K10 K11 K12 K13 pvzI14 K15 K16 K17 K18 K19 K20 K21.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV19l; move HV19l before pvzI2; pose proof (proj2 pvzI2) as HV19r; move HV19r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV35l; move HV35l before pvzI5; pose proof (proj2 pvzI5) as HV35r; move HV35r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV36l; move HV36l before pvzI6; pose proof (proj2 pvzI6) as HV36r; move HV36r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV37l; move HV37l before pvzI7; pose proof (proj2 pvzI7) as HV37r; move HV37r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV38l; move HV38l before pvzI8; pose proof (proj2 pvzI8) as HV38r; move HV38r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV39l; move HV39l before pvzI9; pose proof (proj2 pvzI9) as HV39r; move HV39r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV40l; move HV40l before pvzI10; pose proof (proj2 pvzI10) as HV40r; move HV40r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV41l; move HV41l before pvzI11; pose proof (proj2 pvzI11) as HV41r; move HV41r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K0l; move K0l before pvzI12; pose proof (proj2 pvzI12) as K0r; move K0r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K8l; move K8l before pvzI13; pose proof (proj2 pvzI13) as K8r; move K8r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K14l; move K14l before pvzI14; pose proof (proj2 pvzI14) as K14r; move K14r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_19 := V 19%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 19%nat => Z_to_bv 64 vz_19 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 19%nat => vz_19 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 41%nat => vz_41 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E PbbaG2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbbaG2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbbaG2.kn0).
  { unfold know_ok, PbbaG2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV37l HV37r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV39l HV39r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | clear - HV33l HV33r K8l K8r K17 K18; lia | clear - HV33l HV33r K8l K8r K17 K18; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | clear - HV33l HV33r K8l K8r K17 K18; lia | clear - HV33l HV33r K8l K8r K17 K18; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | clear - HV33l HV33r K8l K8r K17 K18; lia | clear - HV33l HV33r K8l K8r K17 K18; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV19l HV19r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K21]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbbaG2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbbaG2.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 224) <= bv_unsigned a < (vz_2 - 224) + 224) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbbaG2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K18 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbbaG2.ps0) with 0xb03b8 in Hms. change (SR.ps_regs PbbaG2.ps0) with (map (fun i => (i, nth i PbbaG2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbbaG2.ps0) with PbbaG2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbbaG2.regs0 PbbaG2.regs_out0 64 KS_bbaG2 KS_bbaG2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbbaG2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbbaG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG2.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbbaG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG2.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbbaG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG2.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbbaG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbbaG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbbaG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbbaG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG2.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbbaG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG2.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbbaG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG2.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbbaG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG2.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbbaG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG2.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbbaG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K17 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K17 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV19l HV19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV35l HV35r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K17 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV36l HV36r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV37l HV37r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV38l HV38r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV39l HV39r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV19l HV19r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbbaG3 := LibSegBs_bbaG3_u.
Definition KS_bbaG3 : list nat := Eval vm_compute in (BG.kept_list 64 PbbaG3.regs0 PbbaG3.regs_out0).
Lemma KS_bbaG3_ok : BG.kept_ok 64 PbbaG3.regs0 PbbaG3.regs_out0 KS_bbaG3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bbaG3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 19%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 (V 19%nat) ->
  140735332483184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 224) 224 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 36%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 38%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 39%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 40%nat) ->
  140735332483168 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 -> L5.img_clear M 65536 754672 -> L5.u64_at RSEGS M ((V 33%nat) + 392) (V 41%nat) ->
  L5.u64_at RSEGS M ((V 33%nat) + 400) ((V 41%nat) + 320) -> L5.u64_at RSEGS M ((V 33%nat) + 408) ((V 41%nat) + 320) -> 4096 <= (V 41%nat) <= 140737488314328 -> aligned (V 41%nat) 16 ->
  (((V 2%nat) - 224) + 224 <= (V 41%nat) \/ (V 41%nat) + 320 <= ((V 2%nat) - 224)) -> ((V 41%nat) + 320 <= (V 33%nat) \/ (V 33%nat) + 416 <= (V 41%nat)) -> (((V 2%nat) - 224) + 224 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 224)) -> L5.u32_at RSEGS M ((V 2%nat) - 64) 3 ->
  L5.u32_at RSEGS M ((V 2%nat) - 60) (V 19%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) 4 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 224) <= bv_unsigned a < ((V 2%nat) - 224) + 224) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 224) <= i < ((V 2%nat) - 224) + 224) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38918 M) (st fx' R' 0xb03b8 M')
        /\ (forall x, In x KS_bbaG3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 223860
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 192)
        /\ getr R' (reg 8) = Z_to_bv 64 16
        /\ getr R' (reg 9) = Z_to_bv 64 8
        /\ getr R' (reg 10) = Z_to_bv 64 640
        /\ getr R' (reg 11) = Z_to_bv 64 16
        /\ getr R' (reg 12) = Z_to_bv 64 8
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 392)
        /\ getr R' (reg 14) = Z_to_bv 64 14757395258967641293
        /\ getr R' (reg 15) = Z_to_bv 64 461168601842738791
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 2%nat) - 60)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) ((V 2%nat) - 144)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) 223340
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) ((V 33%nat) + 392)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((V 2%nat) - 56)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) ((V 33%nat) + 392)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) 229952
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 19%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 231724
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 39%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 40%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 64) 3
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 60) (V 19%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 G2 G8 G9 G18 G19 pvzI12 K1 K2 K3 K4 K5 K6 K7 pvzI13 K9 K10 K11 K12 K13 pvzI14 K15 K16 K17 K18 K19 K20 K21.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV19l; move HV19l before pvzI2; pose proof (proj2 pvzI2) as HV19r; move HV19r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV35l; move HV35l before pvzI5; pose proof (proj2 pvzI5) as HV35r; move HV35r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV36l; move HV36l before pvzI6; pose proof (proj2 pvzI6) as HV36r; move HV36r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV37l; move HV37l before pvzI7; pose proof (proj2 pvzI7) as HV37r; move HV37r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV38l; move HV38l before pvzI8; pose proof (proj2 pvzI8) as HV38r; move HV38r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV39l; move HV39l before pvzI9; pose proof (proj2 pvzI9) as HV39r; move HV39r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV40l; move HV40l before pvzI10; pose proof (proj2 pvzI10) as HV40r; move HV40r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV41l; move HV41l before pvzI11; pose proof (proj2 pvzI11) as HV41r; move HV41r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K0l; move K0l before pvzI12; pose proof (proj2 pvzI12) as K0r; move K0r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K8l; move K8l before pvzI13; pose proof (proj2 pvzI13) as K8r; move K8r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K14l; move K14l before pvzI14; pose proof (proj2 pvzI14) as K14r; move K14r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_19 := V 19%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 19%nat => Z_to_bv 64 vz_19 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 19%nat => vz_19 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 41%nat => vz_41 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E PbbaG3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbbaG3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbbaG3.kn0).
  { unfold know_ok, PbbaG3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV37l HV37r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV39l HV39r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | clear - HV33l HV33r K8l K8r K17 K18; lia | clear - HV33l HV33r K8l K8r K17 K18; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | clear - HV33l HV33r K8l K8r K17 K18; lia | clear - HV33l HV33r K8l K8r K17 K18; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | clear - HV33l HV33r K8l K8r K17 K18; lia | clear - HV33l HV33r K8l K8r K17 K18; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV19l HV19r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K21]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbbaG3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbbaG3.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 224) <= bv_unsigned a < (vz_2 - 224) + 224) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbbaG3.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K18 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbbaG3.ps0) with 0xb03b8 in Hms. change (SR.ps_regs PbbaG3.ps0) with (map (fun i => (i, nth i PbbaG3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbbaG3.ps0) with PbbaG3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbbaG3.regs0 PbbaG3.regs_out0 64 KS_bbaG3 KS_bbaG3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbbaG3.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbbaG3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG3.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbbaG3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG3.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbbaG3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG3.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbbaG3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbbaG3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbbaG3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG3.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbbaG3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG3.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbbaG3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG3.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbbaG3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG3.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbbaG3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG3.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbbaG3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG3.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbbaG3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K17 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K17 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV19l HV19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV35l HV35r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K17 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV36l HV36r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV37l HV37r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV38l HV38r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV39l HV39r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV19l HV19r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbbaG4 := LibSegBs_bbaG4_u.
Definition KS_bbaG4 : list nat := Eval vm_compute in (BG.kept_list 64 PbbaG4.regs0 PbbaG4.regs_out0).
Lemma KS_bbaG4_ok : BG.kept_ok 64 PbbaG4.regs0 PbbaG4.regs_out0 KS_bbaG4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bbaG4_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 19%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 (V 19%nat) ->
  140735332483184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 224) 224 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 36%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 38%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 39%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 40%nat) ->
  140735332483168 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 -> L5.img_clear M 65536 754672 -> L5.u64_at RSEGS M ((V 33%nat) + 392) (V 41%nat) ->
  L5.u64_at RSEGS M ((V 33%nat) + 400) ((V 41%nat) + 640) -> L5.u64_at RSEGS M ((V 33%nat) + 408) ((V 41%nat) + 640) -> 4096 <= (V 41%nat) <= 140737488314328 -> aligned (V 41%nat) 16 ->
  (((V 2%nat) - 224) + 224 <= (V 41%nat) \/ (V 41%nat) + 640 <= ((V 2%nat) - 224)) -> ((V 41%nat) + 640 <= (V 33%nat) \/ (V 33%nat) + 416 <= (V 41%nat)) -> (((V 2%nat) - 224) + 224 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 224)) -> L5.u32_at RSEGS M ((V 2%nat) - 64) 3 ->
  L5.u32_at RSEGS M ((V 2%nat) - 60) (V 19%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) 4 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 224) <= bv_unsigned a < ((V 2%nat) - 224) + 224) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 224) <= i < ((V 2%nat) - 224) + 224) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38918 M) (st fx' R' 0xb03b8 M')
        /\ (forall x, In x KS_bbaG4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 223860
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 192)
        /\ getr R' (reg 8) = Z_to_bv 64 32
        /\ getr R' (reg 9) = Z_to_bv 64 16
        /\ getr R' (reg 10) = Z_to_bv 64 1280
        /\ getr R' (reg 11) = Z_to_bv 64 32
        /\ getr R' (reg 12) = Z_to_bv 64 16
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 392)
        /\ getr R' (reg 14) = Z_to_bv 64 14757395258967641293
        /\ getr R' (reg 15) = Z_to_bv 64 461168601842738791
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 2%nat) - 60)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) ((V 2%nat) - 144)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) 223340
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) ((V 33%nat) + 392)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((V 2%nat) - 56)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) ((V 33%nat) + 392)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) 229952
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 19%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 231724
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 39%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 40%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 64) 3
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 60) (V 19%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 G2 G8 G9 G18 G19 pvzI12 K1 K2 K3 K4 K5 K6 K7 pvzI13 K9 K10 K11 K12 K13 pvzI14 K15 K16 K17 K18 K19 K20 K21.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV19l; move HV19l before pvzI2; pose proof (proj2 pvzI2) as HV19r; move HV19r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV35l; move HV35l before pvzI5; pose proof (proj2 pvzI5) as HV35r; move HV35r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV36l; move HV36l before pvzI6; pose proof (proj2 pvzI6) as HV36r; move HV36r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV37l; move HV37l before pvzI7; pose proof (proj2 pvzI7) as HV37r; move HV37r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV38l; move HV38l before pvzI8; pose proof (proj2 pvzI8) as HV38r; move HV38r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV39l; move HV39l before pvzI9; pose proof (proj2 pvzI9) as HV39r; move HV39r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV40l; move HV40l before pvzI10; pose proof (proj2 pvzI10) as HV40r; move HV40r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV41l; move HV41l before pvzI11; pose proof (proj2 pvzI11) as HV41r; move HV41r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K0l; move K0l before pvzI12; pose proof (proj2 pvzI12) as K0r; move K0r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K8l; move K8l before pvzI13; pose proof (proj2 pvzI13) as K8r; move K8r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K14l; move K14l before pvzI14; pose proof (proj2 pvzI14) as K14r; move K14r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_19 := V 19%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 19%nat => Z_to_bv 64 vz_19 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 19%nat => vz_19 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 41%nat => vz_41 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E PbbaG4.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbbaG4.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbbaG4.kn0).
  { unfold know_ok, PbbaG4.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV37l HV37r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV39l HV39r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | clear - HV33l HV33r K8l K8r K17 K18; lia | clear - HV33l HV33r K8l K8r K17 K18; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | clear - HV33l HV33r K8l K8r K17 K18; lia | clear - HV33l HV33r K8l K8r K17 K18; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | clear - HV33l HV33r K8l K8r K17 K18; lia | clear - HV33l HV33r K8l K8r K17 K18; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV19l HV19r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K21]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbbaG4.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbbaG4.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 224) <= bv_unsigned a < (vz_2 - 224) + 224) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbbaG4.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K18 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbbaG4.ps0) with 0xb03b8 in Hms. change (SR.ps_regs PbbaG4.ps0) with (map (fun i => (i, nth i PbbaG4.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbbaG4.ps0) with PbbaG4.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbbaG4.regs0 PbbaG4.regs_out0 64 KS_bbaG4 KS_bbaG4_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbbaG4.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbbaG4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG4.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbbaG4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG4.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbbaG4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG4.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbbaG4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG4.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbbaG4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG4.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbbaG4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG4.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbbaG4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG4.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbbaG4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG4.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbbaG4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG4.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbbaG4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG4.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbbaG4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG4.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbbaG4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K17 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K17 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV19l HV19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV35l HV35r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K17 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV36l HV36r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV37l HV37r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV38l HV38r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV39l HV39r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV19l HV19r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbbaG5 := LibSegBs_bbaG5_u.
Definition KS_bbaG5 : list nat := Eval vm_compute in (BG.kept_list 64 PbbaG5.regs0 PbbaG5.regs_out0).
Lemma KS_bbaG5_ok : BG.kept_ok 64 PbbaG5.regs0 PbbaG5.regs_out0 KS_bbaG5 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bbaG5_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 19%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 (V 19%nat) ->
  140735332483184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 224) 224 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 36%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 38%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 39%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 40%nat) ->
  140735332483168 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 -> L5.img_clear M 65536 754672 -> L5.u64_at RSEGS M ((V 33%nat) + 392) (V 41%nat) ->
  L5.u64_at RSEGS M ((V 33%nat) + 400) ((V 41%nat) + 1280) -> L5.u64_at RSEGS M ((V 33%nat) + 408) ((V 41%nat) + 1280) -> 4096 <= (V 41%nat) <= 140737488314328 -> aligned (V 41%nat) 16 ->
  (((V 2%nat) - 224) + 224 <= (V 41%nat) \/ (V 41%nat) + 1280 <= ((V 2%nat) - 224)) -> ((V 41%nat) + 1280 <= (V 33%nat) \/ (V 33%nat) + 416 <= (V 41%nat)) -> (((V 2%nat) - 224) + 224 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 224)) -> L5.u32_at RSEGS M ((V 2%nat) - 64) 3 ->
  L5.u32_at RSEGS M ((V 2%nat) - 60) (V 19%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) 4 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 224) <= bv_unsigned a < ((V 2%nat) - 224) + 224) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 224) <= i < ((V 2%nat) - 224) + 224) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38918 M) (st fx' R' 0xb03b8 M')
        /\ (forall x, In x KS_bbaG5 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 223860
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 192)
        /\ getr R' (reg 8) = Z_to_bv 64 64
        /\ getr R' (reg 9) = Z_to_bv 64 32
        /\ getr R' (reg 10) = Z_to_bv 64 2560
        /\ getr R' (reg 11) = Z_to_bv 64 64
        /\ getr R' (reg 12) = Z_to_bv 64 32
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 392)
        /\ getr R' (reg 14) = Z_to_bv 64 14757395258967641293
        /\ getr R' (reg 15) = Z_to_bv 64 461168601842738791
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 2%nat) - 60)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) ((V 2%nat) - 144)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) 223340
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) ((V 33%nat) + 392)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((V 2%nat) - 56)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) ((V 33%nat) + 392)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) 229952
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 19%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 231724
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 39%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 40%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 64) 3
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 60) (V 19%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 G2 G8 G9 G18 G19 pvzI12 K1 K2 K3 K4 K5 K6 K7 pvzI13 K9 K10 K11 K12 K13 pvzI14 K15 K16 K17 K18 K19 K20 K21.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV19l; move HV19l before pvzI2; pose proof (proj2 pvzI2) as HV19r; move HV19r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV35l; move HV35l before pvzI5; pose proof (proj2 pvzI5) as HV35r; move HV35r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV36l; move HV36l before pvzI6; pose proof (proj2 pvzI6) as HV36r; move HV36r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV37l; move HV37l before pvzI7; pose proof (proj2 pvzI7) as HV37r; move HV37r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV38l; move HV38l before pvzI8; pose proof (proj2 pvzI8) as HV38r; move HV38r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV39l; move HV39l before pvzI9; pose proof (proj2 pvzI9) as HV39r; move HV39r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV40l; move HV40l before pvzI10; pose proof (proj2 pvzI10) as HV40r; move HV40r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV41l; move HV41l before pvzI11; pose proof (proj2 pvzI11) as HV41r; move HV41r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K0l; move K0l before pvzI12; pose proof (proj2 pvzI12) as K0r; move K0r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K8l; move K8l before pvzI13; pose proof (proj2 pvzI13) as K8r; move K8r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K14l; move K14l before pvzI14; pose proof (proj2 pvzI14) as K14r; move K14r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_19 := V 19%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 19%nat => Z_to_bv 64 vz_19 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 19%nat => vz_19 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 41%nat => vz_41 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E PbbaG5.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbbaG5.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbbaG5.kn0).
  { unfold know_ok, PbbaG5.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV37l HV37r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV39l HV39r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | clear - HV33l HV33r K8l K8r K17 K18; lia | clear - HV33l HV33r K8l K8r K17 K18; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | clear - HV33l HV33r K8l K8r K17 K18; lia | clear - HV33l HV33r K8l K8r K17 K18; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | clear - HV33l HV33r K8l K8r K17 K18; lia | clear - HV33l HV33r K8l K8r K17 K18; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV19l HV19r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K21]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbbaG5.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbbaG5.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 224) <= bv_unsigned a < (vz_2 - 224) + 224) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbbaG5.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K18 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbbaG5.ps0) with 0xb03b8 in Hms. change (SR.ps_regs PbbaG5.ps0) with (map (fun i => (i, nth i PbbaG5.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbbaG5.ps0) with PbbaG5.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbbaG5.regs0 PbbaG5.regs_out0 64 KS_bbaG5 KS_bbaG5_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbbaG5.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbbaG5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG5.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbbaG5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG5.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbbaG5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG5.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbbaG5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG5.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbbaG5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG5.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbbaG5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG5.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbbaG5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG5.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbbaG5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG5.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbbaG5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG5.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbbaG5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG5.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbbaG5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG5.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbbaG5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K17 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K17 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV19l HV19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV35l HV35r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K17 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV36l HV36r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV37l HV37r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV38l HV38r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV39l HV39r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV19l HV19r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbbaG6 := LibSegBs_bbaG6_u.
Definition KS_bbaG6 : list nat := Eval vm_compute in (BG.kept_list 64 PbbaG6.regs0 PbbaG6.regs_out0).
Lemma KS_bbaG6_ok : BG.kept_ok 64 PbbaG6.regs0 PbbaG6.regs_out0 KS_bbaG6 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bbaG6_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 19%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 (V 19%nat) ->
  140735332483184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 224) 224 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 36%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 38%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 39%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 40%nat) ->
  140735332483168 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 -> L5.img_clear M 65536 754672 -> L5.u64_at RSEGS M ((V 33%nat) + 392) (V 41%nat) ->
  L5.u64_at RSEGS M ((V 33%nat) + 400) ((V 41%nat) + 2560) -> L5.u64_at RSEGS M ((V 33%nat) + 408) ((V 41%nat) + 2560) -> 4096 <= (V 41%nat) <= 140737488314328 -> aligned (V 41%nat) 16 ->
  (((V 2%nat) - 224) + 224 <= (V 41%nat) \/ (V 41%nat) + 2560 <= ((V 2%nat) - 224)) -> ((V 41%nat) + 2560 <= (V 33%nat) \/ (V 33%nat) + 416 <= (V 41%nat)) -> (((V 2%nat) - 224) + 224 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 224)) -> L5.u32_at RSEGS M ((V 2%nat) - 64) 3 ->
  L5.u32_at RSEGS M ((V 2%nat) - 60) (V 19%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) 4 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 224) <= bv_unsigned a < ((V 2%nat) - 224) + 224) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 224) <= i < ((V 2%nat) - 224) + 224) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38918 M) (st fx' R' 0xb03b8 M')
        /\ (forall x, In x KS_bbaG6 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 223860
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 192)
        /\ getr R' (reg 8) = Z_to_bv 64 128
        /\ getr R' (reg 9) = Z_to_bv 64 64
        /\ getr R' (reg 10) = Z_to_bv 64 5120
        /\ getr R' (reg 11) = Z_to_bv 64 128
        /\ getr R' (reg 12) = Z_to_bv 64 64
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 392)
        /\ getr R' (reg 14) = Z_to_bv 64 14757395258967641293
        /\ getr R' (reg 15) = Z_to_bv 64 461168601842738791
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 2%nat) - 60)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) ((V 2%nat) - 144)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) 223340
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) ((V 33%nat) + 392)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((V 2%nat) - 56)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) ((V 33%nat) + 392)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) 229952
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 19%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 231724
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 39%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 40%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 64) 3
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 60) (V 19%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 G2 G8 G9 G18 G19 pvzI12 K1 K2 K3 K4 K5 K6 K7 pvzI13 K9 K10 K11 K12 K13 pvzI14 K15 K16 K17 K18 K19 K20 K21.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV19l; move HV19l before pvzI2; pose proof (proj2 pvzI2) as HV19r; move HV19r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV35l; move HV35l before pvzI5; pose proof (proj2 pvzI5) as HV35r; move HV35r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV36l; move HV36l before pvzI6; pose proof (proj2 pvzI6) as HV36r; move HV36r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV37l; move HV37l before pvzI7; pose proof (proj2 pvzI7) as HV37r; move HV37r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV38l; move HV38l before pvzI8; pose proof (proj2 pvzI8) as HV38r; move HV38r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV39l; move HV39l before pvzI9; pose proof (proj2 pvzI9) as HV39r; move HV39r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV40l; move HV40l before pvzI10; pose proof (proj2 pvzI10) as HV40r; move HV40r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV41l; move HV41l before pvzI11; pose proof (proj2 pvzI11) as HV41r; move HV41r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K0l; move K0l before pvzI12; pose proof (proj2 pvzI12) as K0r; move K0r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K8l; move K8l before pvzI13; pose proof (proj2 pvzI13) as K8r; move K8r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K14l; move K14l before pvzI14; pose proof (proj2 pvzI14) as K14r; move K14r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_19 := V 19%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 19%nat => Z_to_bv 64 vz_19 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 19%nat => vz_19 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 41%nat => vz_41 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E PbbaG6.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbbaG6.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbbaG6.kn0).
  { unfold know_ok, PbbaG6.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV37l HV37r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV39l HV39r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | clear - HV33l HV33r K8l K8r K17 K18; lia | clear - HV33l HV33r K8l K8r K17 K18; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | clear - HV33l HV33r K8l K8r K17 K18; lia | clear - HV33l HV33r K8l K8r K17 K18; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | clear - HV33l HV33r K8l K8r K17 K18; lia | clear - HV33l HV33r K8l K8r K17 K18; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV19l HV19r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K21]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbbaG6.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbbaG6.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 224) <= bv_unsigned a < (vz_2 - 224) + 224) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbbaG6.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K18 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbbaG6.ps0) with 0xb03b8 in Hms. change (SR.ps_regs PbbaG6.ps0) with (map (fun i => (i, nth i PbbaG6.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbbaG6.ps0) with PbbaG6.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbbaG6.regs0 PbbaG6.regs_out0 64 KS_bbaG6 KS_bbaG6_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbbaG6.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbbaG6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG6.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbbaG6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG6.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbbaG6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG6.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbbaG6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG6.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbbaG6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG6.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbbaG6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG6.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbbaG6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG6.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbbaG6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG6.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbbaG6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG6.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbbaG6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG6.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbbaG6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG6.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbbaG6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K17 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K17 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV19l HV19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV35l HV35r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K17 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV36l HV36r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV37l HV37r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV38l HV38r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV39l HV39r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV19l HV19r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbbaG7 := LibSegBs_bbaG7_u.
Definition KS_bbaG7 : list nat := Eval vm_compute in (BG.kept_list 64 PbbaG7.regs0 PbbaG7.regs_out0).
Lemma KS_bbaG7_ok : BG.kept_ok 64 PbbaG7.regs0 PbbaG7.regs_out0 KS_bbaG7 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bbaG7_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 19%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 (V 19%nat) ->
  140735332483184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 224) 224 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 36%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 38%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 39%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 40%nat) ->
  140735332483168 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 -> L5.img_clear M 65536 754672 -> L5.u64_at RSEGS M ((V 33%nat) + 392) (V 41%nat) ->
  L5.u64_at RSEGS M ((V 33%nat) + 400) ((V 41%nat) + 5120) -> L5.u64_at RSEGS M ((V 33%nat) + 408) ((V 41%nat) + 5120) -> 4096 <= (V 41%nat) <= 140737488314328 -> aligned (V 41%nat) 16 ->
  (((V 2%nat) - 224) + 224 <= (V 41%nat) \/ (V 41%nat) + 5120 <= ((V 2%nat) - 224)) -> ((V 41%nat) + 5120 <= (V 33%nat) \/ (V 33%nat) + 416 <= (V 41%nat)) -> (((V 2%nat) - 224) + 224 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 224)) -> L5.u32_at RSEGS M ((V 2%nat) - 64) 3 ->
  L5.u32_at RSEGS M ((V 2%nat) - 60) (V 19%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) 4 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 224) <= bv_unsigned a < ((V 2%nat) - 224) + 224) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 224) <= i < ((V 2%nat) - 224) + 224) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38918 M) (st fx' R' 0xb03b8 M')
        /\ (forall x, In x KS_bbaG7 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 223860
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 192)
        /\ getr R' (reg 8) = Z_to_bv 64 256
        /\ getr R' (reg 9) = Z_to_bv 64 128
        /\ getr R' (reg 10) = Z_to_bv 64 10240
        /\ getr R' (reg 11) = Z_to_bv 64 256
        /\ getr R' (reg 12) = Z_to_bv 64 128
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 392)
        /\ getr R' (reg 14) = Z_to_bv 64 14757395258967641293
        /\ getr R' (reg 15) = Z_to_bv 64 461168601842738791
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 2%nat) - 60)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) ((V 2%nat) - 144)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) 223340
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) ((V 33%nat) + 392)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((V 2%nat) - 56)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) ((V 33%nat) + 392)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) 229952
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 19%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 231724
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 39%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 40%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 64) 3
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 60) (V 19%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 G2 G8 G9 G18 G19 pvzI12 K1 K2 K3 K4 K5 K6 K7 pvzI13 K9 K10 K11 K12 K13 pvzI14 K15 K16 K17 K18 K19 K20 K21.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV19l; move HV19l before pvzI2; pose proof (proj2 pvzI2) as HV19r; move HV19r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV35l; move HV35l before pvzI5; pose proof (proj2 pvzI5) as HV35r; move HV35r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV36l; move HV36l before pvzI6; pose proof (proj2 pvzI6) as HV36r; move HV36r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV37l; move HV37l before pvzI7; pose proof (proj2 pvzI7) as HV37r; move HV37r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV38l; move HV38l before pvzI8; pose proof (proj2 pvzI8) as HV38r; move HV38r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV39l; move HV39l before pvzI9; pose proof (proj2 pvzI9) as HV39r; move HV39r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV40l; move HV40l before pvzI10; pose proof (proj2 pvzI10) as HV40r; move HV40r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV41l; move HV41l before pvzI11; pose proof (proj2 pvzI11) as HV41r; move HV41r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K0l; move K0l before pvzI12; pose proof (proj2 pvzI12) as K0r; move K0r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K8l; move K8l before pvzI13; pose proof (proj2 pvzI13) as K8r; move K8r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K14l; move K14l before pvzI14; pose proof (proj2 pvzI14) as K14r; move K14r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_19 := V 19%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 19%nat => Z_to_bv 64 vz_19 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 19%nat => vz_19 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 41%nat => vz_41 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E PbbaG7.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbbaG7.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbbaG7.kn0).
  { unfold know_ok, PbbaG7.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV37l HV37r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV39l HV39r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | clear - HV33l HV33r K8l K8r K17 K18; lia | clear - HV33l HV33r K8l K8r K17 K18; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | clear - HV33l HV33r K8l K8r K17 K18; lia | clear - HV33l HV33r K8l K8r K17 K18; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | clear - HV33l HV33r K8l K8r K17 K18; lia | clear - HV33l HV33r K8l K8r K17 K18; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV19l HV19r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K21]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbbaG7.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbbaG7.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 224) <= bv_unsigned a < (vz_2 - 224) + 224) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbbaG7.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K18 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbbaG7.ps0) with 0xb03b8 in Hms. change (SR.ps_regs PbbaG7.ps0) with (map (fun i => (i, nth i PbbaG7.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbbaG7.ps0) with PbbaG7.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbbaG7.regs0 PbbaG7.regs_out0 64 KS_bbaG7 KS_bbaG7_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbbaG7.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbbaG7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG7.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbbaG7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG7.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbbaG7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG7.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbbaG7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG7.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbbaG7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG7.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbbaG7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG7.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbbaG7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG7.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbbaG7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG7.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbbaG7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG7.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbbaG7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG7.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbbaG7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG7.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbbaG7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K17 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K17 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV19l HV19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV35l HV35r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K17 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV36l HV36r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV37l HV37r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV38l HV38r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV39l HV39r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV19l HV19r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbbaG8 := LibSegBs_bbaG8_u.
Definition KS_bbaG8 : list nat := Eval vm_compute in (BG.kept_list 64 PbbaG8.regs0 PbbaG8.regs_out0).
Lemma KS_bbaG8_ok : BG.kept_ok 64 PbbaG8.regs0 PbbaG8.regs_out0 KS_bbaG8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bbaG8_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 19%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 (V 19%nat) ->
  140735332483184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 224) 224 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 36%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 38%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 39%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 40%nat) ->
  140735332483168 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 -> L5.img_clear M 65536 754672 -> L5.u64_at RSEGS M ((V 33%nat) + 392) (V 41%nat) ->
  L5.u64_at RSEGS M ((V 33%nat) + 400) ((V 41%nat) + 10240) -> L5.u64_at RSEGS M ((V 33%nat) + 408) ((V 41%nat) + 10240) -> 4096 <= (V 41%nat) <= 140737488314328 -> aligned (V 41%nat) 16 ->
  (((V 2%nat) - 224) + 224 <= (V 41%nat) \/ (V 41%nat) + 10240 <= ((V 2%nat) - 224)) -> ((V 41%nat) + 10240 <= (V 33%nat) \/ (V 33%nat) + 416 <= (V 41%nat)) -> (((V 2%nat) - 224) + 224 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 224)) -> L5.u32_at RSEGS M ((V 2%nat) - 64) 3 ->
  L5.u32_at RSEGS M ((V 2%nat) - 60) (V 19%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) 4 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 224) <= bv_unsigned a < ((V 2%nat) - 224) + 224) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 224) <= i < ((V 2%nat) - 224) + 224) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38918 M) (st fx' R' 0xb03b8 M')
        /\ (forall x, In x KS_bbaG8 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 223860
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 192)
        /\ getr R' (reg 8) = Z_to_bv 64 512
        /\ getr R' (reg 9) = Z_to_bv 64 256
        /\ getr R' (reg 10) = Z_to_bv 64 20480
        /\ getr R' (reg 11) = Z_to_bv 64 512
        /\ getr R' (reg 12) = Z_to_bv 64 256
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 392)
        /\ getr R' (reg 14) = Z_to_bv 64 14757395258967641293
        /\ getr R' (reg 15) = Z_to_bv 64 461168601842738791
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 2%nat) - 60)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) ((V 2%nat) - 144)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) 223340
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) ((V 33%nat) + 392)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((V 2%nat) - 56)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) ((V 33%nat) + 392)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) 229952
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 19%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 231724
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 39%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 40%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 64) 3
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 60) (V 19%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 G2 G8 G9 G18 G19 pvzI12 K1 K2 K3 K4 K5 K6 K7 pvzI13 K9 K10 K11 K12 K13 pvzI14 K15 K16 K17 K18 K19 K20 K21.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV19l; move HV19l before pvzI2; pose proof (proj2 pvzI2) as HV19r; move HV19r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV35l; move HV35l before pvzI5; pose proof (proj2 pvzI5) as HV35r; move HV35r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV36l; move HV36l before pvzI6; pose proof (proj2 pvzI6) as HV36r; move HV36r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV37l; move HV37l before pvzI7; pose proof (proj2 pvzI7) as HV37r; move HV37r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV38l; move HV38l before pvzI8; pose proof (proj2 pvzI8) as HV38r; move HV38r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV39l; move HV39l before pvzI9; pose proof (proj2 pvzI9) as HV39r; move HV39r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV40l; move HV40l before pvzI10; pose proof (proj2 pvzI10) as HV40r; move HV40r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV41l; move HV41l before pvzI11; pose proof (proj2 pvzI11) as HV41r; move HV41r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K0l; move K0l before pvzI12; pose proof (proj2 pvzI12) as K0r; move K0r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K8l; move K8l before pvzI13; pose proof (proj2 pvzI13) as K8r; move K8r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K14l; move K14l before pvzI14; pose proof (proj2 pvzI14) as K14r; move K14r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_19 := V 19%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 19%nat => Z_to_bv 64 vz_19 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 19%nat => vz_19 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 41%nat => vz_41 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E PbbaG8.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbbaG8.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbbaG8.kn0).
  { unfold know_ok, PbbaG8.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV37l HV37r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV39l HV39r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | clear - HV33l HV33r K8l K8r K17 K18; lia | clear - HV33l HV33r K8l K8r K17 K18; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | clear - HV33l HV33r K8l K8r K17 K18; lia | clear - HV33l HV33r K8l K8r K17 K18; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | clear - HV33l HV33r K8l K8r K17 K18; lia | clear - HV33l HV33r K8l K8r K17 K18; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV19l HV19r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K21]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbbaG8.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbbaG8.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 224) <= bv_unsigned a < (vz_2 - 224) + 224) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbbaG8.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K18 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbbaG8.ps0) with 0xb03b8 in Hms. change (SR.ps_regs PbbaG8.ps0) with (map (fun i => (i, nth i PbbaG8.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbbaG8.ps0) with PbbaG8.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbbaG8.regs0 PbbaG8.regs_out0 64 KS_bbaG8 KS_bbaG8_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbbaG8.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbbaG8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG8.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbbaG8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG8.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbbaG8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG8.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbbaG8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG8.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbbaG8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG8.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbbaG8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG8.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbbaG8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG8.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbbaG8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG8.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbbaG8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG8.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbbaG8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG8.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbbaG8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG8.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbbaG8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K17 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K17 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV19l HV19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV35l HV35r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K17 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV36l HV36r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV37l HV37r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV38l HV38r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV39l HV39r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV19l HV19r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbbaG9 := LibSegBs_bbaG9_u.
Definition KS_bbaG9 : list nat := Eval vm_compute in (BG.kept_list 64 PbbaG9.regs0 PbbaG9.regs_out0).
Lemma KS_bbaG9_ok : BG.kept_ok 64 PbbaG9.regs0 PbbaG9.regs_out0 KS_bbaG9 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bbaG9_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 19%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 (V 19%nat) ->
  140735332483184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 224) 224 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 36%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 38%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 39%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 40%nat) ->
  140735332483168 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 -> L5.img_clear M 65536 754672 -> L5.u64_at RSEGS M ((V 33%nat) + 392) (V 41%nat) ->
  L5.u64_at RSEGS M ((V 33%nat) + 400) ((V 41%nat) + 20480) -> L5.u64_at RSEGS M ((V 33%nat) + 408) ((V 41%nat) + 20480) -> 4096 <= (V 41%nat) <= 140737488314328 -> aligned (V 41%nat) 16 ->
  (((V 2%nat) - 224) + 224 <= (V 41%nat) \/ (V 41%nat) + 20480 <= ((V 2%nat) - 224)) -> ((V 41%nat) + 20480 <= (V 33%nat) \/ (V 33%nat) + 416 <= (V 41%nat)) -> (((V 2%nat) - 224) + 224 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 224)) -> L5.u32_at RSEGS M ((V 2%nat) - 64) 3 ->
  L5.u32_at RSEGS M ((V 2%nat) - 60) (V 19%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) 4 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 224) <= bv_unsigned a < ((V 2%nat) - 224) + 224) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 224) <= i < ((V 2%nat) - 224) + 224) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38918 M) (st fx' R' 0xb03b8 M')
        /\ (forall x, In x KS_bbaG9 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 223860
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 192)
        /\ getr R' (reg 8) = Z_to_bv 64 1024
        /\ getr R' (reg 9) = Z_to_bv 64 512
        /\ getr R' (reg 10) = Z_to_bv 64 40960
        /\ getr R' (reg 11) = Z_to_bv 64 1024
        /\ getr R' (reg 12) = Z_to_bv 64 512
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 392)
        /\ getr R' (reg 14) = Z_to_bv 64 14757395258967641293
        /\ getr R' (reg 15) = Z_to_bv 64 461168601842738791
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 2%nat) - 60)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) ((V 2%nat) - 144)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) 223340
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) ((V 33%nat) + 392)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((V 2%nat) - 56)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) ((V 33%nat) + 392)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) 229952
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 19%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 231724
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 39%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 40%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 64) 3
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 60) (V 19%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 G2 G8 G9 G18 G19 pvzI12 K1 K2 K3 K4 K5 K6 K7 pvzI13 K9 K10 K11 K12 K13 pvzI14 K15 K16 K17 K18 K19 K20 K21.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV19l; move HV19l before pvzI2; pose proof (proj2 pvzI2) as HV19r; move HV19r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV35l; move HV35l before pvzI5; pose proof (proj2 pvzI5) as HV35r; move HV35r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV36l; move HV36l before pvzI6; pose proof (proj2 pvzI6) as HV36r; move HV36r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV37l; move HV37l before pvzI7; pose proof (proj2 pvzI7) as HV37r; move HV37r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV38l; move HV38l before pvzI8; pose proof (proj2 pvzI8) as HV38r; move HV38r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV39l; move HV39l before pvzI9; pose proof (proj2 pvzI9) as HV39r; move HV39r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV40l; move HV40l before pvzI10; pose proof (proj2 pvzI10) as HV40r; move HV40r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV41l; move HV41l before pvzI11; pose proof (proj2 pvzI11) as HV41r; move HV41r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K0l; move K0l before pvzI12; pose proof (proj2 pvzI12) as K0r; move K0r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K8l; move K8l before pvzI13; pose proof (proj2 pvzI13) as K8r; move K8r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K14l; move K14l before pvzI14; pose proof (proj2 pvzI14) as K14r; move K14r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_19 := V 19%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 19%nat => Z_to_bv 64 vz_19 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 19%nat => vz_19 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 41%nat => vz_41 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E PbbaG9.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbbaG9.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbbaG9.kn0).
  { unfold know_ok, PbbaG9.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV37l HV37r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV39l HV39r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | clear - HV33l HV33r K8l K8r K17 K18; lia | clear - HV33l HV33r K8l K8r K17 K18; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | clear - HV33l HV33r K8l K8r K17 K18; lia | clear - HV33l HV33r K8l K8r K17 K18; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | clear - HV33l HV33r K8l K8r K17 K18; lia | clear - HV33l HV33r K8l K8r K17 K18; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV19l HV19r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K21]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbbaG9.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbbaG9.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 224) <= bv_unsigned a < (vz_2 - 224) + 224) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbbaG9.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K18 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbbaG9.ps0) with 0xb03b8 in Hms. change (SR.ps_regs PbbaG9.ps0) with (map (fun i => (i, nth i PbbaG9.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbbaG9.ps0) with PbbaG9.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbbaG9.regs0 PbbaG9.regs_out0 64 KS_bbaG9 KS_bbaG9_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbbaG9.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbbaG9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG9.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbbaG9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG9.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbbaG9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG9.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbbaG9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG9.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbbaG9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG9.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbbaG9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG9.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbbaG9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG9.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbbaG9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG9.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbbaG9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG9.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbbaG9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG9.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbbaG9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG9.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbbaG9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K17 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K17 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV19l HV19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV35l HV35r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K17 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV36l HV36r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV37l HV37r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV38l HV38r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV39l HV39r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV19l HV19r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbbaG10 := LibSegBs_bbaG10_u.
Definition KS_bbaG10 : list nat := Eval vm_compute in (BG.kept_list 64 PbbaG10.regs0 PbbaG10.regs_out0).
Lemma KS_bbaG10_ok : BG.kept_ok 64 PbbaG10.regs0 PbbaG10.regs_out0 KS_bbaG10 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bbaG10_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 19%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 (V 19%nat) ->
  140735332483184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 224) 224 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 36%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 38%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 39%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 40%nat) ->
  140735332483168 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 -> L5.img_clear M 65536 754672 -> L5.u64_at RSEGS M ((V 33%nat) + 392) (V 41%nat) ->
  L5.u64_at RSEGS M ((V 33%nat) + 400) ((V 41%nat) + 40960) -> L5.u64_at RSEGS M ((V 33%nat) + 408) ((V 41%nat) + 40960) -> 4096 <= (V 41%nat) <= 140737488314328 -> aligned (V 41%nat) 16 ->
  (((V 2%nat) - 224) + 224 <= (V 41%nat) \/ (V 41%nat) + 40960 <= ((V 2%nat) - 224)) -> ((V 41%nat) + 40960 <= (V 33%nat) \/ (V 33%nat) + 416 <= (V 41%nat)) -> (((V 2%nat) - 224) + 224 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 224)) -> L5.u32_at RSEGS M ((V 2%nat) - 64) 3 ->
  L5.u32_at RSEGS M ((V 2%nat) - 60) (V 19%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) 4 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 224) <= bv_unsigned a < ((V 2%nat) - 224) + 224) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 224) <= i < ((V 2%nat) - 224) + 224) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38918 M) (st fx' R' 0xb03b8 M')
        /\ (forall x, In x KS_bbaG10 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 223860
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 192)
        /\ getr R' (reg 8) = Z_to_bv 64 2048
        /\ getr R' (reg 9) = Z_to_bv 64 1024
        /\ getr R' (reg 10) = Z_to_bv 64 81920
        /\ getr R' (reg 11) = Z_to_bv 64 2048
        /\ getr R' (reg 12) = Z_to_bv 64 1024
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 392)
        /\ getr R' (reg 14) = Z_to_bv 64 14757395258967641293
        /\ getr R' (reg 15) = Z_to_bv 64 461168601842738791
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 2%nat) - 60)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) ((V 2%nat) - 144)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) 223340
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) ((V 33%nat) + 392)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((V 2%nat) - 56)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) ((V 33%nat) + 392)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) 229952
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 19%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 231724
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 39%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 40%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 64) 3
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 60) (V 19%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 G2 G8 G9 G18 G19 pvzI12 K1 K2 K3 K4 K5 K6 K7 pvzI13 K9 K10 K11 K12 K13 pvzI14 K15 K16 K17 K18 K19 K20 K21.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV19l; move HV19l before pvzI2; pose proof (proj2 pvzI2) as HV19r; move HV19r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV35l; move HV35l before pvzI5; pose proof (proj2 pvzI5) as HV35r; move HV35r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV36l; move HV36l before pvzI6; pose proof (proj2 pvzI6) as HV36r; move HV36r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV37l; move HV37l before pvzI7; pose proof (proj2 pvzI7) as HV37r; move HV37r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV38l; move HV38l before pvzI8; pose proof (proj2 pvzI8) as HV38r; move HV38r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV39l; move HV39l before pvzI9; pose proof (proj2 pvzI9) as HV39r; move HV39r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV40l; move HV40l before pvzI10; pose proof (proj2 pvzI10) as HV40r; move HV40r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV41l; move HV41l before pvzI11; pose proof (proj2 pvzI11) as HV41r; move HV41r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K0l; move K0l before pvzI12; pose proof (proj2 pvzI12) as K0r; move K0r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K8l; move K8l before pvzI13; pose proof (proj2 pvzI13) as K8r; move K8r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K14l; move K14l before pvzI14; pose proof (proj2 pvzI14) as K14r; move K14r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_19 := V 19%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 19%nat => Z_to_bv 64 vz_19 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 19%nat => vz_19 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 41%nat => vz_41 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E PbbaG10.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbbaG10.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbbaG10.kn0).
  { unfold know_ok, PbbaG10.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV37l HV37r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV39l HV39r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | clear - HV33l HV33r K8l K8r K17 K18; lia | clear - HV33l HV33r K8l K8r K17 K18; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | clear - HV33l HV33r K8l K8r K17 K18; lia | clear - HV33l HV33r K8l K8r K17 K18; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | clear - HV33l HV33r K8l K8r K17 K18; lia | clear - HV33l HV33r K8l K8r K17 K18; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K17 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear - HV19l HV19r) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K18; lia | clear - HV2l HV2r K0l K0r K16 K18; lia | exactA K21]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbbaG10.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbbaG10.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 224) <= bv_unsigned a < (vz_2 - 224) + 224) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbbaG10.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K18 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbbaG10.ps0) with 0xb03b8 in Hms. change (SR.ps_regs PbbaG10.ps0) with (map (fun i => (i, nth i PbbaG10.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbbaG10.ps0) with PbbaG10.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbbaG10.regs0 PbbaG10.regs_out0 64 KS_bbaG10 KS_bbaG10_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbbaG10.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbbaG10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG10.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbbaG10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG10.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbbaG10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG10.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbbaG10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG10.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbbaG10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG10.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbbaG10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG10.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbbaG10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG10.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbbaG10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG10.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbbaG10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG10.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbbaG10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG10.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbbaG10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaG10.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbbaG10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K17 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K17 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV19l HV19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV35l HV35r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K17 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV36l HV36r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV37l HV37r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV38l HV38r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV39l HV39r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear - HV19l HV19r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbbaH1 := LibSegBs_bbaH1_u.
Definition KS_bbaH1 : list nat := Eval vm_compute in (BG.kept_list 64 PbbaH1.regs0 PbbaH1.regs_out0).
Lemma KS_bbaH1_ok : BG.kept_ok 64 PbbaH1.regs0 PbbaH1.regs_out0 KS_bbaH1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bbaH1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 19%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 (2 * (V 53%nat)) -> getr R (reg 9) = Z_to_bv 64 (V 53%nat) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 60) -> getr R (reg 19) = Z_to_bv 64 ((V 2%nat) - 64) ->
  140735332483184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 224) 224 -> 140735332483168 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 -> L5.img_clear M 65536 754672 -> L5.u64_at RSEGS M ((V 33%nat) + 392) (V 41%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 400) ((V 41%nat) + (40 * (V 53%nat))) ->
  L5.u64_at RSEGS M ((V 33%nat) + 408) ((V 41%nat) + (40 * (V 53%nat))) -> 4096 <= (V 41%nat) <= 140737488314328 -> aligned (V 41%nat) 16 -> 1 <= (V 53%nat) <= 1024 ->
  4096 <= (V 47%nat) <= 140737488273328 -> aligned (V 47%nat) 16 -> L5.writable RSEGS M (V 47%nat) (80 * (V 53%nat)) -> (((V 2%nat) - 224) + 224 <= (V 41%nat) \/ (V 41%nat) + (40 * (V 53%nat)) <= ((V 2%nat) - 224)) ->
  ((V 41%nat) + (40 * (V 53%nat)) <= (V 33%nat) \/ (V 33%nat) + 416 <= (V 41%nat)) -> (((V 2%nat) - 224) + 224 <= (V 47%nat) \/ (V 47%nat) + (80 * (V 53%nat)) <= ((V 2%nat) - 224)) -> ((V 47%nat) + (80 * (V 53%nat)) <= (V 33%nat) \/ (V 33%nat) + 416 <= (V 47%nat)) -> ((V 47%nat) + (80 * (V 53%nat)) <= (V 41%nat) \/ (V 41%nat) + (40 * (V 53%nat)) <= (V 47%nat)) ->
  L5.defined M (V 41%nat) (40 * (V 53%nat)) -> (((V 2%nat) - 224) + 224 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 224)) -> ((V 47%nat) + (80 * (V 53%nat)) <= 65536 \/ 65536 + 689136 <= (V 47%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 192) ((V 2%nat) - 144) ->
  L5.u64_at RSEGS M ((V 2%nat) - 184) 223340 -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 33%nat) + 392) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 168) ((V 2%nat) - 56) ->
  L5.u64_at RSEGS M ((V 2%nat) - 160) ((V 33%nat) + 392) -> L5.u64_at RSEGS M ((V 2%nat) - 152) 229952 -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 19%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 34%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) 231724 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 36%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 38%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 39%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 40%nat) ->
  L5.u32_at RSEGS M ((V 2%nat) - 64) 3 -> L5.u32_at RSEGS M ((V 2%nat) - 60) (V 19%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) 4 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 224) <= bv_unsigned a < ((V 2%nat) - 224) + 224) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + (80 * (V 53%nat))) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 224) <= i < ((V 2%nat) - 224) + 224) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + (80 * (V 53%nat))) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x36a74 M) (st fx' R' 0xab480 M')
        /\ (forall x, In x KS_bbaH1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 223624
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 176)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 144)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 33%nat) + 392)
        /\ getr R' (reg 10) = (alu64 Instr.ALU_ADD (Z_to_bv 64 (V 47%nat)) (alu64 Instr.ALU_ADD (mul_div Instr.M_MUL (Z_to_bv 64 40) (Z_to_bv 64 (V 53%nat))) (mul_div Instr.M_MUL (Z_to_bv 64 (-8)) (alu64 Instr.ALU_SRA (mul_div Instr.M_MUL (Z_to_bv 64 40) (Z_to_bv 64 (V 53%nat))) (Z_to_bv 64 3)))))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (40 * (V 53%nat))
        /\ getr R' (reg 14) = Z_to_bv 64 40
        /\ getr R' (reg 15) = Z_to_bv 64 ((V 47%nat) + (80 * (V 53%nat)))
        /\ getr R' (reg 16) = Z_to_bv 64 ((V 47%nat) + (40 * (V 53%nat)))
        /\ getr R' (reg 17) = Z_to_bv 64 0
        /\ getr R' (reg 18) = (alu64 Instr.ALU_ADD (Z_to_bv 64 (V 47%nat)) (alu64 Instr.ALU_ADD (mul_div Instr.M_MUL (Z_to_bv 64 40) (Z_to_bv 64 (V 53%nat))) (mul_div Instr.M_MUL (Z_to_bv 64 (-8)) (alu64 Instr.ALU_SRA (mul_div Instr.M_MUL (Z_to_bv 64 40) (Z_to_bv 64 (V 53%nat))) (Z_to_bv 64 3)))))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) ((V 2%nat) - 60)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((V 2%nat) - 56)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) ((V 33%nat) + 392)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) 230028
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) (((V 47%nat) + (40 * (V 53%nat))) + 40)
        /\ L5.u64_at RSEGS M' (((V 47%nat) + (40 * (V 53%nat))) + 32) 0
        /\ L5.u8_at RSEGS M' (((V 47%nat) + (40 * (V 53%nat))) + 24) 0
        /\ L5.u64_at RSEGS M' (((V 47%nat) + (40 * (V 53%nat))) + 16) 4
        /\ L5.u64_at RSEGS M' (((V 47%nat) + (40 * (V 53%nat))) + 8) (bv_unsigned (ext_val true 0 4 (Z_to_bv 64 (V 19%nat))))
        /\ L5.u32_at RSEGS M' ((V 47%nat) + (40 * (V 53%nat))) 3
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) ((V 47%nat) + (80 * (V 53%nat)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) ((V 47%nat) + (40 * (V 53%nat)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) ((V 2%nat) - 144)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) 223340
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) ((V 33%nat) + 392)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 19%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 231724
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 39%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 40%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 64) 3
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 60) (V 19%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 G2 G8 G9 G10 G18 G19 pvzI14 K1 K2 pvzI15 K4 K5 K6 K7 K8 pvzI16 K10 pvzI17 pvzI18 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV19l; move HV19l before pvzI2; pose proof (proj2 pvzI2) as HV19r; move HV19r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV35l; move HV35l before pvzI5; pose proof (proj2 pvzI5) as HV35r; move HV35r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV36l; move HV36l before pvzI6; pose proof (proj2 pvzI6) as HV36r; move HV36r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV37l; move HV37l before pvzI7; pose proof (proj2 pvzI7) as HV37r; move HV37r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV38l; move HV38l before pvzI8; pose proof (proj2 pvzI8) as HV38r; move HV38r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV39l; move HV39l before pvzI9; pose proof (proj2 pvzI9) as HV39r; move HV39r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV40l; move HV40l before pvzI10; pose proof (proj2 pvzI10) as HV40r; move HV40r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV41l; move HV41l before pvzI11; pose proof (proj2 pvzI11) as HV41r; move HV41r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV47l; move HV47l before pvzI12; pose proof (proj2 pvzI12) as HV47r; move HV47r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV53l; move HV53l before pvzI13; pose proof (proj2 pvzI13) as HV53r; move HV53r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K0l; move K0l before pvzI14; pose proof (proj2 pvzI14) as K0r; move K0r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K3l; move K3l before pvzI15; pose proof (proj2 pvzI15) as K3r; move K3r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K9l; move K9l before pvzI16; pose proof (proj2 pvzI16) as K9r; move K9r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K11l; move K11l before pvzI17; pose proof (proj2 pvzI17) as K11r; move K11r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K12l; move K12l before pvzI18; pose proof (proj2 pvzI18) as K12r; move K12r before pvzI18; clear pvzI18.
  set (vz_2 := V 2%nat) in *. set (vz_19 := V 19%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_53 := V 53%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 19%nat => Z_to_bv 64 vz_19 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 47%nat => Z_to_bv 64 vz_47 | 53%nat => Z_to_bv 64 vz_53 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 19%nat => vz_19 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 41%nat => vz_41 | 47%nat => vz_47 | 53%nat => vz_53 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 54%nat. }
  assert (HR: regs_ok E PbbaH1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbbaH1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbbaH1.kn0).
  { unfold know_ok, PbbaH1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K15 K17 K21; lia | clear - HV2l HV2r K0l K0r K15 K17 K21; lia | clear - HV2l HV2r K0l K0r K15 K17 K21; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K16 K18 K21) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K16 K18 K21) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K16 K18 K21) | evalEk ZA ltac:(clear - HV41l HV41r K9l K9r K15 K16 K19) | clear - HV33l HV33r K3l K3r K16 K18 K21; lia | clear - HV33l HV33r K3l K3r K16 K18 K21; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K16 K18 K21) | evalEk ZA ltac:(clear - HV41l HV41r K9l K9r K15 K16 K19 HV53l HV53r K11l K11r K17 K18 K22) | clear - HV33l HV33r K3l K3r K16 K18 K21; lia | clear - HV33l HV33r K3l K3r K16 K18 K21; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K16 K18 K21) | evalEk ZA ltac:(clear - HV41l HV41r K9l K9r K15 K16 K19 HV53l HV53r K11l K11r K17 K18 K22) | clear - HV33l HV33r K3l K3r K16 K18 K21; lia | clear - HV33l HV33r K3l K3r K16 K18 K21; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K9l K9r K15 K16 K19) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K9l K9r K15 K16 K19) | clear; lia | exact K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV53l HV53r K11l K11r K15 K16 K17 K18 K19 K22) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K12l K12r K17 K18 K19 K22) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K12l K12r K17 K18 K19 K22) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K12l K12r K17 K18 K19 K22) | evalEk ZA ltac:(clear - HV53l HV53r K11l K11r K15 K16 K17 K18 K19 K22) | clear - HV47l HV47r K12l K12r K17 K18 K19 K22 HV53l HV53r K11l K11r K15 K16; lia | clear - HV47l HV47r K12l K12r K17 K18 K19 K22 HV53l HV53r K11l K11r K15 K16; lia | clear - HV47l HV47r K12l K12r K17 K18 K19 K22 HV53l HV53r K11l K11r K15 K16; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K9l K9r K15 K16 K19) | evalEk ZA ltac:(clear - HV53l HV53r K11l K11r K15 K16 K17 K18 K19 K22) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV41l HV41r K9l K9r K15 K16 K19) | evalEk ZA ltac:(clear - HV53l HV53r K11l K11r K15 K16 K17 K18 K19 K22) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K16 K18 K21) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K12l K12r K17 K18 K19 K22) | evalEk ZA ltac:(clear - HV53l HV53r K11l K11r K15 K16 K17 K18 K19 K22) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K12l K12r K17 K18 K19 K22) | evalEk ZA ltac:(clear - HV53l HV53r K11l K11r K15 K16 K17 K18 K19 K22) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K16 K18 K21) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K12l K12r K17 K18 K19 K22) | evalEk ZA ltac:(clear - HV53l HV53r K11l K11r K15 K16 K17 K18 K19 K22) | evalEk ZA ltac:(clear - HV41l HV41r K9l K9r K15 K16 K19) | evalEk ZA ltac:(clear - HV53l HV53r K11l K11r K15 K16 K17 K18 K19 K22) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV41l HV41r K9l K9r K15 K16 K19) | evalEk ZA ltac:(clear - HV53l HV53r K11l K11r K15 K16 K17 K18 K19 K22) | clear - HV41l HV41r K9l K9r K15 K16 K19 HV53l HV53r K11l K11r K17 K18 K22; lia | clear - HV41l HV41r K9l K9r K15 K16 K19 HV53l HV53r K11l K11r K17 K18 K22; lia | clear - HV41l HV41r K9l K9r K15 K16 K19 HV53l HV53r K11l K11r K17 K18 K22; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K16 K18 K21) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K12l K12r K17 K18 K19 K22) | evalEk ZA ltac:(clear - HV53l HV53r K11l K11r K15 K16 K17 K18 K19 K22) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | clear - HV2l HV2r K0l K0r K15 K17 K21; lia | clear - HV2l HV2r K0l K0r K15 K17 K21; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K15 K17 K21; lia | clear - HV2l HV2r K0l K0r K15 K17 K21; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K16 K18 K21) | clear - HV2l HV2r K0l K0r K15 K17 K21; lia | clear - HV2l HV2r K0l K0r K15 K17 K21; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K15 K17 K21; lia | clear - HV2l HV2r K0l K0r K15 K17 K21; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | clear - HV2l HV2r K0l K0r K15 K17 K21; lia | clear - HV2l HV2r K0l K0r K15 K17 K21; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K16 K18 K21) | clear - HV2l HV2r K0l K0r K15 K17 K21; lia | clear - HV2l HV2r K0l K0r K15 K17 K21; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K15 K17 K21; lia | clear - HV2l HV2r K0l K0r K15 K17 K21; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk ZA ltac:(clear - HV19l HV19r) | clear - HV2l HV2r K0l K0r K15 K17 K21; lia | clear - HV2l HV2r K0l K0r K15 K17 K21; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K0l K0r K15 K17 K21; lia | clear - HV2l HV2r K0l K0r K15 K17 K21; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk ZA ltac:(clear - HV35l HV35r) | clear - HV2l HV2r K0l K0r K15 K17 K21; lia | clear - HV2l HV2r K0l K0r K15 K17 K21; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K16 K18 K21) | clear - HV2l HV2r K0l K0r K15 K17 K21; lia | clear - HV2l HV2r K0l K0r K15 K17 K21; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K15 K17 K21; lia | clear - HV2l HV2r K0l K0r K15 K17 K21; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K0l K0r K15 K17 K21; lia | clear - HV2l HV2r K0l K0r K15 K17 K21; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk ZA ltac:(clear - HV37l HV37r) | clear - HV2l HV2r K0l K0r K15 K17 K21; lia | clear - HV2l HV2r K0l K0r K15 K17 K21; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV2l HV2r K0l K0r K15 K17 K21; lia | clear - HV2l HV2r K0l K0r K15 K17 K21; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk ZA ltac:(clear - HV39l HV39r) | clear - HV2l HV2r K0l K0r K15 K17 K21; lia | clear - HV2l HV2r K0l K0r K15 K17 K21; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K15 K17 K21; lia | clear - HV2l HV2r K0l K0r K15 K17 K21; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K15 K17 K21; lia | clear - HV2l HV2r K0l K0r K15 K17 K21; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk ZA ltac:(clear - HV19l HV19r) | clear - HV2l HV2r K0l K0r K15 K17 K21; lia | clear - HV2l HV2r K0l K0r K15 K17 K21; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K15 K17 K21; lia | clear - HV2l HV2r K0l K0r K15 K17 K21; lia | exactA K42]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbbaH1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbbaH1.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 224) <= bv_unsigned a < (vz_2 - 224) + 224) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + (80 * vz_53)) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PbbaH1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K15 K17 K21 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K12l K12r K17 K18 K19 K22) | evalEk' ZA Hag ltac:(clear - HV53l HV53r K11l K11r K15 K16 K17 K18 K19 K22) | clear - HV47l HV47r K12l K12r K17 K18 K19 K22 HV53l HV53r K11l K11r K15 K16 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbbaH1.ps0) with 0xab480 in Hms. change (SR.ps_regs PbbaH1.ps0) with (map (fun i => (i, nth i PbbaH1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbbaH1.ps0) with PbbaH1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbbaH1.regs0 PbbaH1.regs_out0 64 KS_bbaH1 KS_bbaH1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbbaH1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbbaH1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaH1.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbbaH1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaH1.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbbaH1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaH1.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbbaH1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaH1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbbaH1.regs_out0]. rewrite (BG.edenot_kept 64 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PbbaH1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbbaH1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaH1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbbaH1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaH1.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbbaH1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaH1.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbbaH1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaH1.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PbbaH1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaH1.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PbbaH1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaH1.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbbaH1.regs_out0]. rewrite (BG.edenot_kept 64 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K16 K18 K21) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K12l K12r K17 K18 K19 K22 HV53l HV53r K11l K11r K15 K16) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K12l K12r K17 K18 K19 K22 HV53l HV53r K11l K11r K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K12l K12r K17 K18 K19 K22 HV53l HV53r K11l K11r K15 K16) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K12l K12r K17 K18 K19 K22 HV53l HV53r K11l K11r K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K12l K12r K17 K18 K19 K22 HV53l HV53r K11l K11r K15 K16) | rewrite (BG.edenot_kept 64 E E' _ Hag) by (vm_compute; reflexivity); reflexivity | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K12l K12r K17 K18 K19 K22 HV53l HV53r K11l K11r K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K12l K12r K17 K18 K19 K22 HV53l HV53r K11l K11r K15 K16) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K12l K12r K17 K18 K19 K22 HV53l HV53r K11l K11r K15 K16) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K12l K12r K17 K18 K19 K22) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K16 K18 K21) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk' ZA Hag ltac:(clear - HV19l HV19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk' ZA Hag ltac:(clear - HV35l HV35r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K16 K18 K21) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk' ZA Hag ltac:(clear - HV36l HV36r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk' ZA Hag ltac:(clear - HV37l HV37r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 23%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk' ZA Hag ltac:(clear - HV38l HV38r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 24%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk' ZA Hag ltac:(clear - HV39l HV39r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 25%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 26%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 27%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk' ZA Hag ltac:(clear - HV19l HV19r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 28%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K15 K17 K21) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbbaH2 := LibSegBs_bbaH2_u.
Definition KS_bbaH2 : list nat := Eval vm_compute in (BG.kept_list 72 PbbaH2.regs0 PbbaH2.regs_out0).
Lemma KS_bbaH2_ok : BG.kept_ok 72 PbbaH2.regs0 PbbaH2.regs_out0 KS_bbaH2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bbaH2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 19%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 176) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + 392) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 2%nat) - 64) ->
  L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 2%nat) - 60) -> L5.u64_at RSEGS M ((V 2%nat) - 168) ((V 2%nat) - 56) -> L5.u64_at RSEGS M ((V 2%nat) - 160) ((V 33%nat) + 392) -> L5.u64_at RSEGS M ((V 2%nat) - 152) 230028 ->
  L5.u64_at RSEGS M ((V 2%nat) - 128) (((V 47%nat) + (40 * (V 53%nat))) + 40) -> L5.u64_at RSEGS M (((V 47%nat) + (40 * (V 53%nat))) + 32) 0 -> L5.u8_at RSEGS M (((V 47%nat) + (40 * (V 53%nat))) + 24) 0 -> L5.u64_at RSEGS M (((V 47%nat) + (40 * (V 53%nat))) + 16) 4 ->
  L5.u64_at RSEGS M (((V 47%nat) + (40 * (V 53%nat))) + 8) (bv_unsigned (ext_val true 0 4 (Z_to_bv 64 (V 19%nat)))) -> L5.u32_at RSEGS M ((V 47%nat) + (40 * (V 53%nat))) 3 -> L5.u64_at RSEGS M ((V 2%nat) - 120) ((V 47%nat) + (80 * (V 53%nat))) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((V 47%nat) + (40 * (V 53%nat))) ->
  L5.u64_at RSEGS M ((V 2%nat) - 144) (V 47%nat) -> 140735332483184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 224) 224 ->
  140735332483168 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 -> L5.img_clear M 65536 754672 -> L5.u64_at RSEGS M ((V 33%nat) + 392) (V 41%nat) ->
  L5.u64_at RSEGS M ((V 33%nat) + 400) ((V 41%nat) + (40 * (V 53%nat))) -> L5.u64_at RSEGS M ((V 33%nat) + 408) ((V 41%nat) + (40 * (V 53%nat))) -> 4096 <= (V 41%nat) <= 140737488314328 -> aligned (V 41%nat) 16 ->
  1 <= (V 53%nat) <= 1024 -> 4096 <= (V 47%nat) <= 140737488273328 -> aligned (V 47%nat) 16 -> L5.writable RSEGS M (V 47%nat) (80 * (V 53%nat)) ->
  (((V 2%nat) - 224) + 224 <= (V 41%nat) \/ (V 41%nat) + (40 * (V 53%nat)) <= ((V 2%nat) - 224)) -> ((V 41%nat) + (40 * (V 53%nat)) <= (V 33%nat) \/ (V 33%nat) + 416 <= (V 41%nat)) -> (((V 2%nat) - 224) + 224 <= (V 47%nat) \/ (V 47%nat) + (80 * (V 53%nat)) <= ((V 2%nat) - 224)) -> ((V 47%nat) + (80 * (V 53%nat)) <= (V 33%nat) \/ (V 33%nat) + 416 <= (V 47%nat)) ->
  ((V 47%nat) + (80 * (V 53%nat)) <= (V 41%nat) \/ (V 41%nat) + (40 * (V 53%nat)) <= (V 47%nat)) -> L5.defined M (V 41%nat) (40 * (V 53%nat)) -> (((V 2%nat) - 224) + 224 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 224)) -> ((V 47%nat) + (80 * (V 53%nat)) <= 65536 \/ 65536 + 689136 <= (V 47%nat)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 192) ((V 2%nat) - 144) -> L5.u64_at RSEGS M ((V 2%nat) - 184) 223340 -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 33%nat) + 392) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 19%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 96) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) 231724 ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 36%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 38%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 39%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 40%nat) -> L5.u32_at RSEGS M ((V 2%nat) - 64) 3 -> L5.u32_at RSEGS M ((V 2%nat) - 60) (V 19%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) 4 ->
  L5.writable RSEGS M ((V 33%nat) + 392) 24 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 224) <= bv_unsigned a < ((V 2%nat) - 224) + 224) -> ~ (((V 33%nat) + 392) <= bv_unsigned a < ((V 33%nat) + 392) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 224) <= i < ((V 2%nat) - 224) + 224) -> ~ (((V 33%nat) + 392) <= i < ((V 33%nat) + 392) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x36988 M) (st fx' R' 0x56720 M')
        /\ (forall x, In x KS_bbaH2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 230040
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 144)
        /\ getr R' (reg 8) = Z_to_bv 64 (((V 47%nat) + (40 * (V 53%nat))) + 40)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 56)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (40 * (V 53%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 2%nat) - 60)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) ((V 41%nat) + (40 * (V 53%nat)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 41%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 408) ((V 47%nat) + (80 * (V 53%nat)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) (V 41%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 400) (((V 47%nat) + (40 * (V 53%nat))) + 40)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 41%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 392) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) ((V 2%nat) - 60)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((V 2%nat) - 56)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) ((V 33%nat) + 392)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) 230028
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) ((V 2%nat) - 144)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) 223340
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) ((V 33%nat) + 392)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 19%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 231724
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 39%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 40%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 64) 3
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 60) (V 19%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 G2 G8 G9 G18 G19 K0 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 pvzI14 K14 K15 pvzI15 K17 K18 K19 K20 K21 pvzI16 K23 pvzI17 pvzI18 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV19l; move HV19l before pvzI2; pose proof (proj2 pvzI2) as HV19r; move HV19r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV35l; move HV35l before pvzI5; pose proof (proj2 pvzI5) as HV35r; move HV35r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV36l; move HV36l before pvzI6; pose proof (proj2 pvzI6) as HV36r; move HV36r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV37l; move HV37l before pvzI7; pose proof (proj2 pvzI7) as HV37r; move HV37r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV38l; move HV38l before pvzI8; pose proof (proj2 pvzI8) as HV38r; move HV38r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV39l; move HV39l before pvzI9; pose proof (proj2 pvzI9) as HV39r; move HV39r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV40l; move HV40l before pvzI10; pose proof (proj2 pvzI10) as HV40r; move HV40r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV41l; move HV41l before pvzI11; pose proof (proj2 pvzI11) as HV41r; move HV41r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV47l; move HV47l before pvzI12; pose proof (proj2 pvzI12) as HV47r; move HV47r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV53l; move HV53l before pvzI13; pose proof (proj2 pvzI13) as HV53r; move HV53r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K13l; move K13l before pvzI14; pose proof (proj2 pvzI14) as K13r; move K13r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K16l; move K16l before pvzI15; pose proof (proj2 pvzI15) as K16r; move K16r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K22l; move K22l before pvzI16; pose proof (proj2 pvzI16) as K22r; move K22r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K24l; move K24l before pvzI17; pose proof (proj2 pvzI17) as K24r; move K24r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K25l; move K25l before pvzI18; pose proof (proj2 pvzI18) as K25r; move K25r before pvzI18; clear pvzI18.
  set (vz_2 := V 2%nat) in *. set (vz_19 := V 19%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_53 := V 53%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 19%nat => Z_to_bv 64 vz_19 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 47%nat => Z_to_bv 64 vz_47 | 53%nat => Z_to_bv 64 vz_53 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 19%nat => vz_19 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 41%nat => vz_41 | 47%nat => vz_47 | 53%nat => vz_53 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 54%nat. }
  assert (HR: regs_ok E PbbaH2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbbaH2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbbaH2.kn0).
  { unfold know_ok, PbbaH2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk ZA ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | exactA K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk ZA ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk ZA ltac:(clear - HV33l HV33r K16l K16r K29 K31 K34) | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk ZA ltac:(clear - HV47l HV47r K25l K25r K30 K31 K32 K35 HV53l HV53r K24l K24r K28 K29) | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K25l K25r K30 K31 K32 K35 HV53l HV53r K24l K24r K28 K29) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K25l K25r K30 K31 K32 K35 HV53l HV53r K24l K24r K28 K29; lia | clear - HV47l HV47r K25l K25r K30 K31 K32 K35 HV53l HV53r K24l K24r K28 K29; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV47l HV47r K25l K25r K30 K31 K32 K35 HV53l HV53r K24l K24r K28 K29) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K25l K25r K30 K31 K32 K35 HV53l HV53r K24l K24r K28 K29; lia | clear - HV47l HV47r K25l K25r K30 K31 K32 K35 HV53l HV53r K24l K24r K28 K29; lia | byte_tac ltac:(clear) | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K25l K25r K30 K31 K32 K35 HV53l HV53r K24l K24r K28 K29) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K25l K25r K30 K31 K32 K35 HV53l HV53r K24l K24r K28 K29; lia | clear - HV47l HV47r K25l K25r K30 K31 K32 K35 HV53l HV53r K24l K24r K28 K29; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K25l K25r K30 K31 K32 K35 HV53l HV53r K24l K24r K28 K29) | cbn [edenot ev]; reflexivity | clear - HV47l HV47r K25l K25r K30 K31 K32 K35 HV53l HV53r K24l K24r K28 K29; lia | clear - HV47l HV47r K25l K25r K30 K31 K32 K35 HV53l HV53r K24l K24r K28 K29; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV47l HV47r K25l K25r K30 K31 K32 K35 HV53l HV53r K24l K24r K28 K29) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K25l K25r K30 K31 K32 K35 HV53l HV53r K24l K24r K28 K29; lia | clear - HV47l HV47r K25l K25r K30 K31 K32 K35 HV53l HV53r K24l K24r K28 K29; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk ZA ltac:(clear - HV47l HV47r K25l K25r K30 K31 K32 K35 HV53l HV53r K24l K24r K28 K29) | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk ZA ltac:(clear - HV47l HV47r K25l K25r K30 K31 K32 K35 HV53l HV53r K24l K24r K28 K29) | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk ZA ltac:(clear - HV47l HV47r K25l K25r K30 K31 K32 K35) | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K16l K16r K29 K31 K34) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K16l K16r K29 K31 K34) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K16l K16r K29 K31 K34) | evalEk ZA ltac:(clear - HV41l HV41r K22l K22r K28 K29 K32) | clear - HV33l HV33r K16l K16r K29 K31 K34; lia | clear - HV33l HV33r K16l K16r K29 K31 K34; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K16l K16r K29 K31 K34) | evalEk ZA ltac:(clear - HV41l HV41r K22l K22r K28 K29 K32 HV53l HV53r K24l K24r K30 K31 K35) | clear - HV33l HV33r K16l K16r K29 K31 K34; lia | clear - HV33l HV33r K16l K16r K29 K31 K34; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K16l K16r K29 K31 K34) | evalEk ZA ltac:(clear - HV41l HV41r K22l K22r K28 K29 K32 HV53l HV53r K24l K24r K30 K31 K35) | clear - HV33l HV33r K16l K16r K29 K31 K34; lia | clear - HV33l HV33r K16l K16r K29 K31 K34; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K22l K22r K28 K29 K32) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K22l K22r K28 K29 K32) | clear; lia | exact K23]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV53l HV53r K24l K24r K28 K29 K30 K31 K32 K35) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K25l K25r K30 K31 K32 K35) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K25l K25r K30 K31 K32 K35) | clear; lia | exact K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K25l K25r K30 K31 K32 K35) | evalEk ZA ltac:(clear - HV53l HV53r K24l K24r K28 K29 K30 K31 K32 K35) | clear - HV47l HV47r K25l K25r K30 K31 K32 K35 HV53l HV53r K24l K24r K28 K29; lia | clear - HV47l HV47r K25l K25r K30 K31 K32 K35 HV53l HV53r K24l K24r K28 K29; lia | clear - HV47l HV47r K25l K25r K30 K31 K32 K35 HV53l HV53r K24l K24r K28 K29; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K22l K22r K28 K29 K32) | evalEk ZA ltac:(clear - HV53l HV53r K24l K24r K28 K29 K30 K31 K32 K35) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV41l HV41r K22l K22r K28 K29 K32) | evalEk ZA ltac:(clear - HV53l HV53r K24l K24r K28 K29 K30 K31 K32 K35) | evalEk ZA ltac:(clear - HV33l HV33r K16l K16r K29 K31 K34) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K25l K25r K30 K31 K32 K35) | evalEk ZA ltac:(clear - HV53l HV53r K24l K24r K28 K29 K30 K31 K32 K35) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K25l K25r K30 K31 K32 K35) | evalEk ZA ltac:(clear - HV53l HV53r K24l K24r K28 K29 K30 K31 K32 K35) | evalEk ZA ltac:(clear - HV33l HV33r K16l K16r K29 K31 K34) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K25l K25r K30 K31 K32 K35) | evalEk ZA ltac:(clear - HV53l HV53r K24l K24r K28 K29 K30 K31 K32 K35) | evalEk ZA ltac:(clear - HV41l HV41r K22l K22r K28 K29 K32) | evalEk ZA ltac:(clear - HV53l HV53r K24l K24r K28 K29 K30 K31 K32 K35) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV41l HV41r K22l K22r K28 K29 K32) | evalEk ZA ltac:(clear - HV53l HV53r K24l K24r K28 K29 K30 K31 K32 K35) | clear - HV41l HV41r K22l K22r K28 K29 K32 HV53l HV53r K24l K24r K30 K31 K35; lia | clear - HV41l HV41r K22l K22r K28 K29 K32 HV53l HV53r K24l K24r K30 K31 K35; lia | clear - HV41l HV41r K22l K22r K28 K29 K32 HV53l HV53r K24l K24r K30 K31 K35; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K16l K16r K29 K31 K34) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K25l K25r K30 K31 K32 K35) | evalEk ZA ltac:(clear - HV53l HV53r K24l K24r K28 K29 K30 K31 K32 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk ZA ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk ZA ltac:(clear - HV33l HV33r K16l K16r K29 K31 K34) | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk ZA ltac:(clear - HV19l HV19r) | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk ZA ltac:(clear - HV35l HV35r) | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk ZA ltac:(clear - HV33l HV33r K16l K16r K29 K31 K34) | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk ZA ltac:(clear - HV37l HV37r) | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk ZA ltac:(clear - HV39l HV39r) | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | exactA K49]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk ZA ltac:(clear - HV19l HV19r) | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | exactA K50]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | clear - HV2l HV2r K13l K13r K28 K30 K34; lia | exactA K51]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K16l K16r K29 K31 K34) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K16l K16r K29 K31 K34; lia | clear - HV33l HV33r K16l K16r K29 K31 K34; lia | clear - HV33l HV33r K16l K16r K29 K31 K34; lia | exactA K52]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbbaH2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbbaH2.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 224) <= bv_unsigned a < (vz_2 - 224) + 224) -> ~ ((vz_33 + 392) <= bv_unsigned a < (vz_33 + 392) + 24) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PbbaH2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K13l K13r K28 K30 K34 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K16l K16r K29 K31 K34) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K16l K16r K29 K31 K34 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbbaH2.ps0) with 0x56720 in Hms. change (SR.ps_regs PbbaH2.ps0) with (map (fun i => (i, nth i PbbaH2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbbaH2.ps0) with PbbaH2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbbaH2.regs0 PbbaH2.regs_out0 72 KS_bbaH2 KS_bbaH2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbbaH2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbbaH2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaH2.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbbaH2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaH2.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbbaH2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaH2.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbbaH2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaH2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbbaH2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaH2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbbaH2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaH2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbbaH2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaH2.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbbaH2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaH2.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbbaH2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk' ZA Hag ltac:(clear - HV41l HV41r K22l K22r K28 K29 K32 HV53l HV53r K24l K24r K30 K31 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk' ZA Hag ltac:(clear - HV41l HV41r K22l K22r K28 K29 K32) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K16l K16r K29 K31 K34) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K25l K25r K30 K31 K32 K35 HV53l HV53r K24l K24r K28 K29) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk' ZA Hag ltac:(clear - HV41l HV41r K22l K22r K28 K29 K32) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K16l K16r K29 K31 K34) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K25l K25r K30 K31 K32 K35 HV53l HV53r K24l K24r K28 K29) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk' ZA Hag ltac:(clear - HV41l HV41r K22l K22r K28 K29 K32) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K16l K16r K29 K31 K34) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K25l K25r K30 K31 K32 K35) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K16l K16r K29 K31 K34) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K16l K16r K29 K31 K34) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk' ZA Hag ltac:(clear - HV19l HV19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk' ZA Hag ltac:(clear - HV35l HV35r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K16l K16r K29 K31 K34) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk' ZA Hag ltac:(clear - HV36l HV36r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk' ZA Hag ltac:(clear - HV37l HV37r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk' ZA Hag ltac:(clear - HV38l HV38r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk' ZA Hag ltac:(clear - HV39l HV39r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 23%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 24%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 25%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk' ZA Hag ltac:(clear - HV19l HV19r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 26%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K13l K13r K28 K30 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbbaT := LibSegBs_bbaT_u.
Definition KS_bbaT : list nat := Eval vm_compute in (BG.kept_list 72 PbbaT.regs0 PbbaT.regs_out0).
Lemma KS_bbaT_ok : BG.kept_ok 72 PbbaT.regs0 PbbaT.regs_out0 KS_bbaT = true. Proof. vm_compute. reflexivity. Qed.
Lemma bbaT_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 19%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 8) = Z_to_bv 64 (((V 47%nat) + (40 * (V 53%nat))) + 40) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 56) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 60) -> getr R (reg 19) = Z_to_bv 64 ((V 2%nat) - 64) ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) ((V 41%nat) + (40 * (V 53%nat))) -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 41%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 408) ((V 47%nat) + (80 * (V 53%nat))) -> L5.u64_at RSEGS M ((V 2%nat) - 128) (V 41%nat) ->
  L5.u64_at RSEGS M ((V 33%nat) + 400) (((V 47%nat) + (40 * (V 53%nat))) + 40) -> L5.u64_at RSEGS M ((V 2%nat) - 136) (V 41%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 392) (V 47%nat) -> L5.u64_at RSEGS M (((V 47%nat) + (40 * (V 53%nat))) + 32) 0 ->
  L5.u8_at RSEGS M (((V 47%nat) + (40 * (V 53%nat))) + 24) 0 -> L5.u64_at RSEGS M (((V 47%nat) + (40 * (V 53%nat))) + 16) 4 -> L5.u64_at RSEGS M (((V 47%nat) + (40 * (V 53%nat))) + 8) (bv_unsigned (ext_val true 0 4 (Z_to_bv 64 (V 19%nat)))) -> L5.u32_at RSEGS M ((V 47%nat) + (40 * (V 53%nat))) 3 ->
  140735332483184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 224) 224 -> 140735332483168 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 -> L5.img_clear M 65536 754672 -> 4096 <= (V 41%nat) <= 140737488314328 -> aligned (V 41%nat) 16 ->
  1 <= (V 53%nat) <= 1024 -> 4096 <= (V 47%nat) <= 140737488273328 -> aligned (V 47%nat) 16 -> L5.writable RSEGS M (V 47%nat) (80 * (V 53%nat)) ->
  (((V 2%nat) - 224) + 224 <= (V 41%nat) \/ (V 41%nat) + (40 * (V 53%nat)) <= ((V 2%nat) - 224)) -> ((V 41%nat) + (40 * (V 53%nat)) <= (V 33%nat) \/ (V 33%nat) + 416 <= (V 41%nat)) -> (((V 2%nat) - 224) + 224 <= (V 47%nat) \/ (V 47%nat) + (80 * (V 53%nat)) <= ((V 2%nat) - 224)) -> ((V 47%nat) + (80 * (V 53%nat)) <= (V 33%nat) \/ (V 33%nat) + 416 <= (V 47%nat)) ->
  ((V 47%nat) + (80 * (V 53%nat)) <= (V 41%nat) \/ (V 41%nat) + (40 * (V 53%nat)) <= (V 47%nat)) -> (((V 2%nat) - 224) + 224 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 224)) -> ((V 47%nat) + (80 * (V 53%nat)) <= 65536 \/ 65536 + 689136 <= (V 47%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 33%nat) + 392) ->
  L5.u64_at RSEGS M ((V 2%nat) - 104) (V 19%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 72) 231724 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 36%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 38%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 39%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 40%nat) -> L5.u32_at RSEGS M ((V 2%nat) - 64) 3 -> L5.u32_at RSEGS M ((V 2%nat) - 60) (V 19%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) 4 -> L5.writable RSEGS M ((V 33%nat) + 392) 24 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 400) <= bv_unsigned a < ((V 33%nat) + 400) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 400) <= i < ((V 33%nat) + 400) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38298 M) (st fx' R' 0x38960 M')
        /\ (forall x, In x KS_bbaT -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 40
        /\ getr R' (reg 18) = Z_to_bv 64 (V 39%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 400) (((V 47%nat) + (40 * (V 53%nat))) + 40)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 G2 G8 G9 G18 G19 K0 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 pvzI14 K13 K14 pvzI15 K16 K17 pvzI16 K19 pvzI17 pvzI18 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV19l; move HV19l before pvzI2; pose proof (proj2 pvzI2) as HV19r; move HV19r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV35l; move HV35l before pvzI5; pose proof (proj2 pvzI5) as HV35r; move HV35r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV36l; move HV36l before pvzI6; pose proof (proj2 pvzI6) as HV36r; move HV36r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV37l; move HV37l before pvzI7; pose proof (proj2 pvzI7) as HV37r; move HV37r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV38l; move HV38l before pvzI8; pose proof (proj2 pvzI8) as HV38r; move HV38r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV39l; move HV39l before pvzI9; pose proof (proj2 pvzI9) as HV39r; move HV39r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV40l; move HV40l before pvzI10; pose proof (proj2 pvzI10) as HV40r; move HV40r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV41l; move HV41l before pvzI11; pose proof (proj2 pvzI11) as HV41r; move HV41r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV47l; move HV47l before pvzI12; pose proof (proj2 pvzI12) as HV47r; move HV47r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV53l; move HV53l before pvzI13; pose proof (proj2 pvzI13) as HV53r; move HV53r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K12l; move K12l before pvzI14; pose proof (proj2 pvzI14) as K12r; move K12r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K15l; move K15l before pvzI15; pose proof (proj2 pvzI15) as K15r; move K15r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K18l; move K18l before pvzI16; pose proof (proj2 pvzI16) as K18r; move K18r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K20l; move K20l before pvzI17; pose proof (proj2 pvzI17) as K20r; move K20r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K21l; move K21l before pvzI18; pose proof (proj2 pvzI18) as K21r; move K21r before pvzI18; clear pvzI18.
  set (vz_2 := V 2%nat) in *. set (vz_19 := V 19%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_53 := V 53%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 19%nat => Z_to_bv 64 vz_19 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 47%nat => Z_to_bv 64 vz_47 | 53%nat => Z_to_bv 64 vz_53 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 19%nat => vz_19 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 41%nat => vz_41 | 47%nat => vz_47 | 53%nat => vz_53 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 54%nat. }
  assert (HR: regs_ok E PbbaT.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbbaT.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbbaT.kn0).
  { unfold know_ok, PbbaT.kn0.
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K12l K12r K24 K26 K29) | evalEk ZA ltac:(clear - HV41l HV41r K18l K18r K24 K25 K28 HV53l HV53r K20l K20r K26 K27 K30) | clear - HV2l HV2r K12l K12r K24 K26 K29; lia | clear - HV2l HV2r K12l K12r K24 K26 K29; lia | exactA K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K12l K12r K24 K26 K29) | evalEk ZA ltac:(clear - HV41l HV41r K18l K18r K24 K25 K28) | clear - HV2l HV2r K12l K12r K24 K26 K29; lia | clear - HV2l HV2r K12l K12r K24 K26 K29; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K15l K15r K25 K27 K29) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r K26 K27 K28 K30 HV53l HV53r K20l K20r K24 K25) | clear - HV33l HV33r K15l K15r K25 K27 K29; lia | clear - HV33l HV33r K15l K15r K25 K27 K29; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K12l K12r K24 K26 K29) | evalEk ZA ltac:(clear - HV41l HV41r K18l K18r K24 K25 K28) | clear - HV2l HV2r K12l K12r K24 K26 K29; lia | clear - HV2l HV2r K12l K12r K24 K26 K29; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K15l K15r K25 K27 K29) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r K26 K27 K28 K30 HV53l HV53r K20l K20r K24 K25) | clear - HV33l HV33r K15l K15r K25 K27 K29; lia | clear - HV33l HV33r K15l K15r K25 K27 K29; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K12l K12r K24 K26 K29) | evalEk ZA ltac:(clear - HV41l HV41r K18l K18r K24 K25 K28) | clear - HV2l HV2r K12l K12r K24 K26 K29; lia | clear - HV2l HV2r K12l K12r K24 K26 K29; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K15l K15r K25 K27 K29) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r K26 K27 K28 K30) | clear - HV33l HV33r K15l K15r K25 K27 K29; lia | clear - HV33l HV33r K15l K15r K25 K27 K29; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r K26 K27 K28 K30 HV53l HV53r K20l K20r K24 K25) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K21l K21r K26 K27 K28 K30 HV53l HV53r K20l K20r K24 K25; lia | clear - HV47l HV47r K21l K21r K26 K27 K28 K30 HV53l HV53r K20l K20r K24 K25; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r K26 K27 K28 K30 HV53l HV53r K20l K20r K24 K25) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K21l K21r K26 K27 K28 K30 HV53l HV53r K20l K20r K24 K25; lia | clear - HV47l HV47r K21l K21r K26 K27 K28 K30 HV53l HV53r K20l K20r K24 K25; lia | byte_tac ltac:(clear) | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r K26 K27 K28 K30 HV53l HV53r K20l K20r K24 K25) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K21l K21r K26 K27 K28 K30 HV53l HV53r K20l K20r K24 K25; lia | clear - HV47l HV47r K21l K21r K26 K27 K28 K30 HV53l HV53r K20l K20r K24 K25; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r K26 K27 K28 K30 HV53l HV53r K20l K20r K24 K25) | cbn [edenot ev]; reflexivity | clear - HV47l HV47r K21l K21r K26 K27 K28 K30 HV53l HV53r K20l K20r K24 K25; lia | clear - HV47l HV47r K21l K21r K26 K27 K28 K30 HV53l HV53r K20l K20r K24 K25; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r K26 K27 K28 K30 HV53l HV53r K20l K20r K24 K25) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K21l K21r K26 K27 K28 K30 HV53l HV53r K20l K20r K24 K25; lia | clear - HV47l HV47r K21l K21r K26 K27 K28 K30 HV53l HV53r K20l K20r K24 K25; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K12l K12r K24 K26 K29) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K12l K12r K24 K26 K29) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K12l K12r K24 K26 K29) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K12l K12r K24 K26 K29; lia | clear - HV2l HV2r K12l K12r K24 K26 K29; lia | clear - HV2l HV2r K12l K12r K24 K26 K29; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K15l K15r K25 K27 K29) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K15l K15r K25 K27 K29) | clear; lia | exact K16]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K18l K18r K24 K25 K28) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K18l K18r K24 K25 K28) | clear; lia | exact K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV53l HV53r K20l K20r K24 K25 K26 K27 K28 K30) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r K26 K27 K28 K30) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r K26 K27 K28 K30) | clear; lia | exact K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r K26 K27 K28 K30) | evalEk ZA ltac:(clear - HV53l HV53r K20l K20r K24 K25 K26 K27 K28 K30) | clear - HV47l HV47r K21l K21r K26 K27 K28 K30 HV53l HV53r K20l K20r K24 K25; lia | clear - HV47l HV47r K21l K21r K26 K27 K28 K30 HV53l HV53r K20l K20r K24 K25; lia | clear - HV47l HV47r K21l K21r K26 K27 K28 K30 HV53l HV53r K20l K20r K24 K25; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K12l K12r K24 K26 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K18l K18r K24 K25 K28) | evalEk ZA ltac:(clear - HV53l HV53r K20l K20r K24 K25 K26 K27 K28 K30) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV41l HV41r K18l K18r K24 K25 K28) | evalEk ZA ltac:(clear - HV53l HV53r K20l K20r K24 K25 K26 K27 K28 K30) | evalEk ZA ltac:(clear - HV33l HV33r K15l K15r K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K12l K12r K24 K26 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r K26 K27 K28 K30) | evalEk ZA ltac:(clear - HV53l HV53r K20l K20r K24 K25 K26 K27 K28 K30) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r K26 K27 K28 K30) | evalEk ZA ltac:(clear - HV53l HV53r K20l K20r K24 K25 K26 K27 K28 K30) | evalEk ZA ltac:(clear - HV33l HV33r K15l K15r K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r K26 K27 K28 K30) | evalEk ZA ltac:(clear - HV53l HV53r K20l K20r K24 K25 K26 K27 K28 K30) | evalEk ZA ltac:(clear - HV41l HV41r K18l K18r K24 K25 K28) | evalEk ZA ltac:(clear - HV53l HV53r K20l K20r K24 K25 K26 K27 K28 K30) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K12l K12r K24 K26 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K15l K15r K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r K26 K27 K28 K30) | evalEk ZA ltac:(clear - HV53l HV53r K20l K20r K24 K25 K26 K27 K28 K30) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K12l K12r K24 K26 K29) | evalEk ZA ltac:(clear - HV33l HV33r K15l K15r K25 K27 K29) | clear - HV2l HV2r K12l K12r K24 K26 K29; lia | clear - HV2l HV2r K12l K12r K24 K26 K29; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K12l K12r K24 K26 K29) | evalEk ZA ltac:(clear - HV19l HV19r) | clear - HV2l HV2r K12l K12r K24 K26 K29; lia | clear - HV2l HV2r K12l K12r K24 K26 K29; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K12l K12r K24 K26 K29) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K12l K12r K24 K26 K29; lia | clear - HV2l HV2r K12l K12r K24 K26 K29; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K12l K12r K24 K26 K29) | evalEk ZA ltac:(clear - HV35l HV35r) | clear - HV2l HV2r K12l K12r K24 K26 K29; lia | clear - HV2l HV2r K12l K12r K24 K26 K29; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K12l K12r K24 K26 K29) | evalEk ZA ltac:(clear - HV33l HV33r K15l K15r K25 K27 K29) | clear - HV2l HV2r K12l K12r K24 K26 K29; lia | clear - HV2l HV2r K12l K12r K24 K26 K29; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K12l K12r K24 K26 K29) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K12l K12r K24 K26 K29; lia | clear - HV2l HV2r K12l K12r K24 K26 K29; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K12l K12r K24 K26 K29) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K12l K12r K24 K26 K29; lia | clear - HV2l HV2r K12l K12r K24 K26 K29; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K12l K12r K24 K26 K29) | evalEk ZA ltac:(clear - HV37l HV37r) | clear - HV2l HV2r K12l K12r K24 K26 K29; lia | clear - HV2l HV2r K12l K12r K24 K26 K29; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K12l K12r K24 K26 K29) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV2l HV2r K12l K12r K24 K26 K29; lia | clear - HV2l HV2r K12l K12r K24 K26 K29; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K12l K12r K24 K26 K29) | evalEk ZA ltac:(clear - HV39l HV39r) | clear - HV2l HV2r K12l K12r K24 K26 K29; lia | clear - HV2l HV2r K12l K12r K24 K26 K29; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K12l K12r K24 K26 K29) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K12l K12r K24 K26 K29; lia | clear - HV2l HV2r K12l K12r K24 K26 K29; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K12l K12r K24 K26 K29) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K12l K12r K24 K26 K29; lia | clear - HV2l HV2r K12l K12r K24 K26 K29; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K12l K12r K24 K26 K29) | evalEk ZA ltac:(clear - HV19l HV19r) | clear - HV2l HV2r K12l K12r K24 K26 K29; lia | clear - HV2l HV2r K12l K12r K24 K26 K29; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K12l K12r K24 K26 K29) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K12l K12r K24 K26 K29; lia | clear - HV2l HV2r K12l K12r K24 K26 K29; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K15l K15r K25 K27 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K15l K15r K25 K27 K29; lia | clear - HV33l HV33r K15l K15r K25 K27 K29; lia | clear - HV33l HV33r K15l K15r K25 K27 K29; lia | exactA K45]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbbaT.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbbaT.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_33 + 400) <= bv_unsigned a < (vz_33 + 400) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbbaT.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K15l K15r K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K15l K15r K25 K27 K29 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbbaT.ps0) with 0x38960 in Hms. change (SR.ps_regs PbbaT.ps0) with (map (fun i => (i, nth i PbbaT.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbbaT.ps0) with PbbaT.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbbaT.regs0 PbbaT.regs_out0 72 KS_bbaT KS_bbaT_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbbaT.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbbaT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaT.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbbaT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaT.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbbaT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaT.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbbaT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaT.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbbaT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaT.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbbaT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaT.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbbaT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaT.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbbaT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K15l K15r K25 K27 K29) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r K26 K27 K28 K30 HV53l HV53r K20l K20r K24 K25) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbbaE := LibSegBs_bbaE_u.
Definition KS_bbaE : list nat := Eval vm_compute in (BG.kept_list 64 PbbaE.regs0 PbbaE.regs_out0).
Lemma KS_bbaE_ok : BG.kept_ok 64 PbbaE.regs0 PbbaE.regs_out0 KS_bbaE = true. Proof. vm_compute. reflexivity. Qed.
Lemma bbaE_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483168 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 36%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 38%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 39%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 40%nat) ->
  140735332483168 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 -> (((V 2%nat) - 96) + 96 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 96)) -> L5.writable RSEGS M ((V 33%nat) + 8) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38978 M) (st fx' R' 0x38960 M')
        /\ (forall x, In x KS_bbaE -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 39%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 40%nat)
        /\ L5.u8_at RSEGS M' ((V 33%nat) + 8) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G8 G9 G18 pvzI10 K1 K2 K3 K4 K5 K6 K7 pvzI11 K9 K10 K11.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV37l; move HV37l before pvzI6; pose proof (proj2 pvzI6) as HV37r; move HV37r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV38l; move HV38l before pvzI7; pose proof (proj2 pvzI7) as HV38r; move HV38r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV39l; move HV39l before pvzI8; pose proof (proj2 pvzI8) as HV39r; move HV39r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV40l; move HV40l before pvzI9; pose proof (proj2 pvzI9) as HV40r; move HV40r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K0l; move K0l before pvzI10; pose proof (proj2 pvzI10) as K0r; move K0r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K8l; move K8l before pvzI11; pose proof (proj2 pvzI11) as K8r; move K8r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 41%nat. }
  assert (HR: regs_ok E PbbaE.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbbaE.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbbaE.kn0).
  { unfold know_ok, PbbaE.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear - HV37l HV37r) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear - HV39l HV39r) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K10) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K10) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K10) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K10) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K8l K8r K10; lia | clear - HV33l HV33r K8l K8r K10; lia | clear - HV33l HV33r K8l K8r K10; lia | exactA K11]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbbaE.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbbaE.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_33 + 8) <= bv_unsigned a < (vz_33 + 8) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbbaE.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K10) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K8l K8r K10 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbbaE.ps0) with 0x38960 in Hms. change (SR.ps_regs PbbaE.ps0) with (map (fun i => (i, nth i PbbaE.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbbaE.ps0) with PbbaE.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbbaE.regs0 PbbaE.regs_out0 64 KS_bbaE KS_bbaE_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbbaE.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbbaE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaE.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbbaE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaE.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbbaE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaE.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbbaE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaE.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbbaE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaE.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbbaE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K10) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

End PNSBAP.
