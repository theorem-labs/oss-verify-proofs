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
     BigLinkBase. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import BigLinkGlue_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import L5Kn_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.seg Require LibSegBs_dkRH_u LibSegBs_dkRF_u LibSegBs_dkL0_u LibSegBs_dkL1_u LibSegBs_dkL2_u LibSegBs_dkL3_u LibSegBs_dkRM_u LibSegBs_dkRD0_u LibSegBs_dkRD1_u LibSegBs_dkRD2_u LibSegBs_dkRD3_u LibSegBs_dkRT_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNSDRP.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5K.zpoly Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
  intros A Pz. rewrite (BG.word_of_unsigned (edenot E e) (z mod BL.MM) (L5K.zpoly_sound E Vz e z A Pz)).
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
  first [ rewrite Z.mod_small; [ first [reflexivity | k; lia] | k; L5K.zrange_tac ]
        | symmetry; eapply (Z.mod_unique_pos _ _ (-1)); k; unfold BL.MM; lia
        | symmetry; eapply (Z.mod_unique_pos _ _ 1); k; unfold BL.MM; lia ].
(* [comment removed for export] *)
Local Ltac pvz_hg tac := lazymatch goal with |- ?G0 => let PG := fresh "PGoal" in set (PG := G0); tac; subst PG end.
Local Ltac pvz_fold B k := lazymatch B with | ?A2 /\ ?B2 => pvz_fold B2 ltac:(fun T2 => let T := fresh "pvzT" in pose (T := A2 /\ T2); k T) | _ => k B end.
Local Ltac pvz_linconj := lazymatch goal with |- ?A /\ ?B => pvz_fold B ltac:(fun T => change_no_check (A /\ T)) | _ => idtac end.
Local Ltac pvz_unfold ZA := lazymatch type of ZA with forall j, _ = ?f j => tryif is_var f then unfold f else idtac | _ => idtac end.
Tactic Notation "evalEk" constr(ZA) tactic(k) :=
  L5K.norm_expr; eapply L5K.zpoly_val; [ apply (L5K.zagree_all _ _ _ ZA) | cbn [L5K.zpoly]; pvz_unfold ZA; reflexivity | solve_modk k ].
Tactic Notation "evalEk'" constr(ZA) constr(AG) tactic(k) :=
  L5K.norm_expr; eapply L5K.zpoly_val;
  [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity] | cbn [L5K.zpoly]; pvz_unfold ZA; reflexivity | solve_modk k ].
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
Local Ltac slotP ZA :=
  first [ assumption | reflexivity
        | (etransitivity; [eassumption|]; symmetry; eapply word_of_zpoly; [apply (L5K.zagree_all _ _ _ ZA) | cbn [L5K.zpoly]; pvz_unfold ZA; f_equal; clear; lia]) ].
(* [comment removed for export] *)
Local Ltac wordP' ZA AG :=
  eapply word_of_zpoly; [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity]
                        | cbn [L5K.zpoly]; pvz_unfold ZA; f_equal; clear; lia ].
(* [comment removed for export] *)
Module PdkRH := LibSegBs_dkRH_u.
Definition KS_dkRH : list nat := Eval vm_compute in (BG.kept_list 80 PdkRH.regs0 PdkRH.regs_out0).
Lemma KS_dkRH_ok : BG.kept_ok 80 PdkRH.regs0 PdkRH.regs_out0 KS_dkRH = true. Proof. vm_compute. reflexivity. Qed.
Lemma dkRH_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 5) = Z_to_bv 64 18446744073709551607 -> getr R (reg 6) = Z_to_bv 64 18446744073709551603 -> getr R (reg 7) = Z_to_bv 64 19342813113834067 -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 42) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + (V 38%nat)) -> getr R (reg 12) = Z_to_bv 64 (3 - (V 40%nat)) -> getr R (reg 13) = Z_to_bv 64 ((V 2%nat) - 240) -> getr R (reg 14) = Z_to_bv 64 (((V 2%nat) - 184) + (36 * (V 40%nat))) -> getr R (reg 15) = Z_to_bv 64 18446744073709551580 -> getr R (reg 16) = Z_to_bv 64 ((V 2%nat) - 216) -> getr R (reg 17) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 19) = Z_to_bv 64 (V 40%nat) -> getr R (reg 28) = Z_to_bv 64 1000000000 -> getr R (reg 29) = Z_to_bv 64 14757395259826634752 -> getr R (reg 30) = Z_to_bv 64 10 ->
  140735332483312 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) ->
  4096 <= (V 33%nat) <= 140737488355286 -> L5.writable RSEGS M (V 33%nat) 42 -> (((V 2%nat) - 18432) + 18432 <= (V 33%nat) \/ (V 33%nat) + 42 <= ((V 2%nat) - 18432)) -> L5.img_clear M 65536 754672 ->
  0 <= (V 40%nat) <= 3 -> 0 <= (V 38%nat) <= 1 -> L5.u64_at RSEGS M ((V 2%nat) - 232) (V 41%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 224) (V 42%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 256) <= bv_unsigned a < ((V 2%nat) - 256) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 256) <= i < ((V 2%nat) - 256) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38bc4 M) (st fx' R' 0x38bd8 M')
        /\ (forall x, In x KS_dkRH -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 20) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 31) = Z_to_bv 64 (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 248) (V 42%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) (V 41%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 G2 G5 G6 G7 G8 G9 G12 G13 G14 G15 G16 G17 G18 G19 G28 G29 G30 pvzI16 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 pvzI17 K13 K14 K15 pvzI18 pvzI19 K18 K19.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV40l; move HV40l before pvzI4; pose proof (proj2 pvzI4) as HV40r; move HV40r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV41l; move HV41l before pvzI5; pose proof (proj2 pvzI5) as HV41r; move HV41r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV42l; move HV42l before pvzI6; pose proof (proj2 pvzI6) as HV42r; move HV42r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV60l; move HV60l before pvzI7; pose proof (proj2 pvzI7) as HV60r; move HV60r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV61l; move HV61l before pvzI8; pose proof (proj2 pvzI8) as HV61r; move HV61r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV62l; move HV62l before pvzI9; pose proof (proj2 pvzI9) as HV62r; move HV62r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV63l; move HV63l before pvzI10; pose proof (proj2 pvzI10) as HV63r; move HV63r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV64l; move HV64l before pvzI11; pose proof (proj2 pvzI11) as HV64r; move HV64r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV65l; move HV65l before pvzI12; pose proof (proj2 pvzI12) as HV65r; move HV65r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV66l; move HV66l before pvzI13; pose proof (proj2 pvzI13) as HV66r; move HV66r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV67l; move HV67l before pvzI14; pose proof (proj2 pvzI14) as HV67r; move HV67r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV68l; move HV68l before pvzI15; pose proof (proj2 pvzI15) as HV68r; move HV68r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K0l; move K0l before pvzI16; pose proof (proj2 pvzI16) as K0r; move K0r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K12l; move K12l before pvzI17; pose proof (proj2 pvzI17) as K12r; move K12r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K16l; move K16l before pvzI18; pose proof (proj2 pvzI18) as K16r; move K16r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K17l; move K17l before pvzI19; pose proof (proj2 pvzI19) as K17r; move K17r before pvzI19; clear pvzI19.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 38%nat => Z_to_bv 64 vz_38 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 38%nat => vz_38 | 40%nat => vz_40 | 41%nat => vz_41 | 42%nat => vz_42 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 69%nat. }
  assert (HR: regs_ok E PdkRH.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdkRH.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdkRH.kn0).
  { unfold know_ok, PdkRH.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV61l HV61r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV63l HV63r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K12l K12r K14; lia | clear - HV33l HV33r K12l K12r K14; lia | clear - HV33l HV33r K12l K12r K14; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV41l HV41r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K19]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PdkRH.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PdkRH.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 256) <= bv_unsigned a < (vz_2 - 256) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PdkRH.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K14 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PdkRH.ps0) with 0x38bd8 in Hms. change (SR.ps_regs PdkRH.ps0) with (map (fun i => (i, nth i PdkRH.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PdkRH.ps0) with PdkRH.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkRH.regs0 PdkRH.regs_out0 80 KS_dkRH KS_dkRH_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PdkRH.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PdkRH.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkRH.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PdkRH.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkRH.regs_out0 E' R' 31 Hregs) by (clear; lia). cbn [nth PdkRH.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk' ZA Hag ltac:(clear - HV42l HV42r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk' ZA Hag ltac:(clear - HV41l HV41r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PdkRF := LibSegBs_dkRF_u.
Definition KS_dkRF_0 : list nat := Eval vm_compute in (BG.kept_list 80 PdkRF.regs0 PdkRF.regs_out0).
Lemma KS_dkRF_0_ok : BG.kept_ok 80 PdkRF.regs0 PdkRF.regs_out0 KS_dkRF_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_dkRF_1 : list nat := Eval vm_compute in (BG.kept_list 80 PdkRF.regs0 PdkRF.regs_out1).
Lemma KS_dkRF_1_ok : BG.kept_ok 80 PdkRF.regs0 PdkRF.regs_out1 KS_dkRF_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_dkRF_2 : list nat := Eval vm_compute in (BG.kept_list 80 PdkRF.regs0 PdkRF.regs_out2).
Lemma KS_dkRF_2_ok : BG.kept_ok 80 PdkRF.regs0 PdkRF.regs_out2 KS_dkRF_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_dkRF_3 : list nat := Eval vm_compute in (BG.kept_list 80 PdkRF.regs0 PdkRF.regs_out3).
Lemma KS_dkRF_3_ok : BG.kept_ok 80 PdkRF.regs0 PdkRF.regs_out3 KS_dkRF_3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dkRF_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 5) = Z_to_bv 64 18446744073709551607 -> getr R (reg 6) = Z_to_bv 64 18446744073709551603 -> getr R (reg 7) = Z_to_bv 64 19342813113834067 -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 42) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + (V 38%nat)) -> getr R (reg 12) = Z_to_bv 64 (3 - (V 40%nat)) -> getr R (reg 13) = Z_to_bv 64 ((V 2%nat) - 240) -> getr R (reg 14) = Z_to_bv 64 (((V 2%nat) - 184) + (36 * (V 40%nat))) -> getr R (reg 15) = Z_to_bv 64 18446744073709551580 -> getr R (reg 16) = Z_to_bv 64 ((V 2%nat) - 216) -> getr R (reg 17) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 19) = Z_to_bv 64 (V 40%nat) -> getr R (reg 20) = Z_to_bv 64 (V 42%nat) -> getr R (reg 21) = Z_to_bv 64 (V 41%nat) -> getr R (reg 28) = Z_to_bv 64 1000000000 -> getr R (reg 29) = Z_to_bv 64 14757395259826634752 -> getr R (reg 30) = Z_to_bv 64 10 -> getr R (reg 31) = Z_to_bv 64 (V 40%nat) ->
  140735332483312 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) ->
  4096 <= (V 33%nat) <= 140737488355286 -> L5.writable RSEGS M (V 33%nat) 42 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 42 <= ((V 2%nat) - 256)) -> L5.img_clear M 65536 754672 ->
  0 <= (V 40%nat) <= 3 -> 0 <= (V 38%nat) <= 1 -> L5.u64_at RSEGS M ((V 2%nat) - 256) (V 41%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 248) (V 42%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 232) <= bv_unsigned a < ((V 2%nat) - 232) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 232) <= i < ((V 2%nat) - 232) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x38bd8 M) (st fx' R' 0x38c84 M')
        /\ (forall x, In x KS_dkRF_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 19) = Z_to_bv 64 (V 41%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) (V 42%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) (V 41%nat)
        /\ ((((V 42%nat) / 4294967296) - 0) mod 2 ^ 64) < 1
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | 63%nat => Z_to_bv 64 (V 63%nat) | 64%nat => Z_to_bv 64 (V 64%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 66%nat => Z_to_bv 64 (V 66%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EVar 42) (ELit 0)) (ELit 0)) (ELit 1))) <= 1
        /\ (((V 41%nat) - 0) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0x38bd8 M) (st fx' R' 0x38c1c M')
        /\ (forall x, In x KS_dkRF_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 19) = Z_to_bv 64 (((V 2%nat) + (36 * (V 40%nat))) - 220)
        /\ getr R' (reg 20) = Z_to_bv 64 0
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 2%nat) - 256)
        /\ 1 <= ((((V 42%nat) / 4294967296) - 0) mod 2 ^ 64)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | 63%nat => Z_to_bv 64 (V 63%nat) | 64%nat => Z_to_bv 64 (V 64%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 66%nat => Z_to_bv 64 (V 66%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EVar 42) (ELit 0)) (ELit 0)) (ELit 1))) <= 1
        /\ (((V 41%nat) - 0) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0x38bd8 M) (st fx' R' 0x38c1c M')
        /\ (forall x, In x KS_dkRF_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 19) = Z_to_bv 64 (((V 2%nat) + (36 * (V 40%nat))) - 220)
        /\ getr R' (reg 20) = Z_to_bv 64 0
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 2%nat) - 256)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | 63%nat => Z_to_bv 64 (V 63%nat) | 64%nat => Z_to_bv 64 (V 64%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 66%nat => Z_to_bv 64 (V 66%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EVar 42) (ELit 0)) (ELit 0)) (ELit 1))) <= 0
        /\ (((V 41%nat) - 0) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0x38bd8 M) (st fx' R' 0x38c1c M')
        /\ (forall x, In x KS_dkRF_3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 19) = Z_to_bv 64 (((V 2%nat) + (36 * (V 40%nat))) - 220)
        /\ getr R' (reg 20) = Z_to_bv 64 0
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 2%nat) - 256)
        /\ 1 <= (((V 41%nat) - 0) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 G2 G5 G6 G7 G8 G9 G12 G13 G14 G15 G16 G17 G18 G19 G20 G21 G28 G29 G30 G31 pvzI16 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 pvzI17 K13 K14 K15 pvzI18 pvzI19 K18 K19.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV40l; move HV40l before pvzI4; pose proof (proj2 pvzI4) as HV40r; move HV40r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV41l; move HV41l before pvzI5; pose proof (proj2 pvzI5) as HV41r; move HV41r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV42l; move HV42l before pvzI6; pose proof (proj2 pvzI6) as HV42r; move HV42r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV60l; move HV60l before pvzI7; pose proof (proj2 pvzI7) as HV60r; move HV60r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV61l; move HV61l before pvzI8; pose proof (proj2 pvzI8) as HV61r; move HV61r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV62l; move HV62l before pvzI9; pose proof (proj2 pvzI9) as HV62r; move HV62r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV63l; move HV63l before pvzI10; pose proof (proj2 pvzI10) as HV63r; move HV63r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV64l; move HV64l before pvzI11; pose proof (proj2 pvzI11) as HV64r; move HV64r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV65l; move HV65l before pvzI12; pose proof (proj2 pvzI12) as HV65r; move HV65r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV66l; move HV66l before pvzI13; pose proof (proj2 pvzI13) as HV66r; move HV66r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV67l; move HV67l before pvzI14; pose proof (proj2 pvzI14) as HV67r; move HV67r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV68l; move HV68l before pvzI15; pose proof (proj2 pvzI15) as HV68r; move HV68r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K0l; move K0l before pvzI16; pose proof (proj2 pvzI16) as K0r; move K0r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K12l; move K12l before pvzI17; pose proof (proj2 pvzI17) as K12r; move K12r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K16l; move K16l before pvzI18; pose proof (proj2 pvzI18) as K16r; move K16r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K17l; move K17l before pvzI19; pose proof (proj2 pvzI19) as K17r; move K17r before pvzI19; clear pvzI19.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 38%nat => Z_to_bv 64 vz_38 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 38%nat => vz_38 | 40%nat => vz_40 | 41%nat => vz_41 | 42%nat => vz_42 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 69%nat. }
  assert (HR: regs_ok E PdkRF.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdkRF.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdkRF.kn0).
  { unfold know_ok, PdkRF.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV61l HV61r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV63l HV63r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K12l K12r K14; lia | clear - HV33l HV33r K12l K12r K14; lia | clear - HV33l HV33r K12l K12r K14; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV41l HV41r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K19]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PdkRF.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PdkRF.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 232) <= bv_unsigned a < (vz_2 - 232) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PdkRF.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K14 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PdkRF.ps0) with 0x38c84 in Hms. change (SR.ps_regs PdkRF.ps0) with (map (fun i => (i, nth i PdkRF.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PdkRF.ps0) with PdkRF.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkRF.regs0 PdkRF.regs_out0 80 KS_dkRF_0 KS_dkRF_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PdkRF.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PdkRF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk' ZA Hag ltac:(clear - HV42l HV42r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk' ZA Hag ltac:(clear - HV41l HV41r) | clear; lia]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3); reflexivity | rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 4); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. left.
    change (SR.ps_pc PdkRF.ps1) with 0x38c1c in Hms. change (SR.ps_regs PdkRF.ps1) with (map (fun i => (i, nth i PdkRF.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PdkRF.ps1) with PdkRF.cells1 in Hcells. unfold PdkRF.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkRF.regs0 PdkRF.regs_out1 80 KS_dkRF_1 KS_dkRF_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PdkRF.regs_out1 E' R' 19 Hregs) by (clear; lia). cbn [nth PdkRF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkRF.regs_out1 E' R' 20 Hregs) by (clear; lia). cbn [nth PdkRF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkRF.regs_out1 E' R' 21 Hregs) by (clear; lia). cbn [nth PdkRF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1); reflexivity | rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. left.
    change (SR.ps_pc PdkRF.ps2) with 0x38c1c in Hms. change (SR.ps_regs PdkRF.ps2) with (map (fun i => (i, nth i PdkRF.regs_out2 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PdkRF.ps2) with PdkRF.cells2 in Hcells. unfold PdkRF.cells2 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkRF.regs0 PdkRF.regs_out2 80 KS_dkRF_2 KS_dkRF_2_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PdkRF.regs_out2 E' R' 19 Hregs) by (clear; lia). cbn [nth PdkRF.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkRF.regs_out2 E' R' 20 Hregs) by (clear; lia). cbn [nth PdkRF.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkRF.regs_out2 E' R' 21 Hregs) by (clear; lia). cbn [nth PdkRF.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0); reflexivity | rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. 
    change (SR.ps_pc PdkRF.ps3) with 0x38c1c in Hms. change (SR.ps_regs PdkRF.ps3) with (map (fun i => (i, nth i PdkRF.regs_out3 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PdkRF.ps3) with PdkRF.cells3 in Hcells. unfold PdkRF.cells3 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkRF.regs0 PdkRF.regs_out3 80 KS_dkRF_3 KS_dkRF_3_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PdkRF.regs_out3 E' R' 19 Hregs) by (clear; lia). cbn [nth PdkRF.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkRF.regs_out3 E' R' 20 Hregs) by (clear; lia). cbn [nth PdkRF.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkRF.regs_out3 E' R' 21 Hregs) by (clear; lia). cbn [nth PdkRF.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PdkL0 := LibSegBs_dkL0_u.
Definition KS_dkL0 : list nat := Eval vm_compute in (BG.kept_list 80 PdkL0.regs0 PdkL0.regs_out0).
Lemma KS_dkL0_ok : BG.kept_ok 80 PdkL0.regs0 PdkL0.regs_out0 KS_dkL0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dkL0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 5) = Z_to_bv 64 18446744073709551607 -> getr R (reg 6) = Z_to_bv 64 18446744073709551603 -> getr R (reg 7) = Z_to_bv 64 19342813113834067 -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 42) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + (V 38%nat)) -> getr R (reg 12) = Z_to_bv 64 (3 - (V 40%nat)) -> getr R (reg 13) = Z_to_bv 64 ((V 2%nat) - 240) -> getr R (reg 14) = Z_to_bv 64 (((V 2%nat) - 184) + (36 * (V 40%nat))) -> getr R (reg 15) = Z_to_bv 64 18446744073709551580 -> getr R (reg 16) = Z_to_bv 64 ((V 2%nat) - 216) -> getr R (reg 17) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 20) = Z_to_bv 64 (V 44%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 28) = Z_to_bv 64 1000000000 -> getr R (reg 29) = Z_to_bv 64 14757395259826634752 -> getr R (reg 30) = Z_to_bv 64 10 -> getr R (reg 31) = Z_to_bv 64 (V 40%nat) ->
  140735332483312 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) ->
  4096 <= (V 33%nat) <= 140737488355286 -> L5.writable RSEGS M (V 33%nat) 42 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 42 <= ((V 2%nat) - 256)) -> L5.img_clear M 65536 754672 ->
  0 <= (V 40%nat) <= 3 -> 0 <= (V 38%nat) <= 1 -> 0 <= (V 44%nat) <= 999999999 -> L5.u32_at RSEGS M ((V 2%nat) - 256) (V 45%nat) ->
  0 <= (V 45%nat) <= 4294967295 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 256) <= bv_unsigned a < ((V 2%nat) - 256) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 256) <= i < ((V 2%nat) - 256) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38c1c M) (st fx' R' 0x38c1c M')
        /\ (forall x, In x KS_dkL0 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 20)) = ((((4294967296 * (V 44%nat)) mod 2 ^ 64) + (((V 45%nat) + ((18446744072709551616 * ((((((((4294967296 * (V 44%nat)) mod 2 ^ 64) + (V 45%nat)) mod 2 ^ 64) / 512) * 19342813113834067) / 2 ^ 64) / 2048)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 2%nat) - 252)
        /\ bv_unsigned (getr R' (reg 22)) = ((1000000000 * ((((((((4294967296 * (V 44%nat)) mod 2 ^ 64) + (V 45%nat)) mod 2 ^ 64) / 512) * 19342813113834067) / 2 ^ 64) / 2048)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 256) ((((((((4294967296 * (V 44%nat)) mod 2 ^ 64) + (V 45%nat)) mod 2 ^ 64) / 512) * 19342813113834067) / 2 ^ 64) / 2048)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 G2 G5 G6 G7 G8 G9 G12 G13 G14 G15 G16 G17 G18 G20 G21 G28 G29 G30 G31 pvzI16 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 pvzI17 K13 K14 K15 pvzI18 pvzI19 pvzI20 K19 pvzI21.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV40l; move HV40l before pvzI4; pose proof (proj2 pvzI4) as HV40r; move HV40r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV44l; move HV44l before pvzI5; pose proof (proj2 pvzI5) as HV44r; move HV44r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV45l; move HV45l before pvzI6; pose proof (proj2 pvzI6) as HV45r; move HV45r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV60l; move HV60l before pvzI7; pose proof (proj2 pvzI7) as HV60r; move HV60r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV61l; move HV61l before pvzI8; pose proof (proj2 pvzI8) as HV61r; move HV61r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV62l; move HV62l before pvzI9; pose proof (proj2 pvzI9) as HV62r; move HV62r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV63l; move HV63l before pvzI10; pose proof (proj2 pvzI10) as HV63r; move HV63r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV64l; move HV64l before pvzI11; pose proof (proj2 pvzI11) as HV64r; move HV64r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV65l; move HV65l before pvzI12; pose proof (proj2 pvzI12) as HV65r; move HV65r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV66l; move HV66l before pvzI13; pose proof (proj2 pvzI13) as HV66r; move HV66r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV67l; move HV67l before pvzI14; pose proof (proj2 pvzI14) as HV67r; move HV67r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV68l; move HV68l before pvzI15; pose proof (proj2 pvzI15) as HV68r; move HV68r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K0l; move K0l before pvzI16; pose proof (proj2 pvzI16) as K0r; move K0r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K12l; move K12l before pvzI17; pose proof (proj2 pvzI17) as K12r; move K12r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K16l; move K16l before pvzI18; pose proof (proj2 pvzI18) as K16r; move K16r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K17l; move K17l before pvzI19; pose proof (proj2 pvzI19) as K17r; move K17r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K18l; move K18l before pvzI20; pose proof (proj2 pvzI20) as K18r; move K18r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K20l; move K20l before pvzI21; pose proof (proj2 pvzI21) as K20r; move K20r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 38%nat => Z_to_bv 64 vz_38 | 40%nat => Z_to_bv 64 vz_40 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 38%nat => vz_38 | 40%nat => vz_40 | 44%nat => vz_44 | 45%nat => vz_45 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 69%nat. }
  assert (HR: regs_ok E PdkL0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdkL0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdkL0.kn0).
  { unfold know_ok, PdkL0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV61l HV61r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV63l HV63r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K12l K12r K14; lia | clear - HV33l HV33r K12l K12r K14; lia | clear - HV33l HV33r K12l K12r K14; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV44l HV44r K18l K18r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV45l HV45r K20l K20r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PdkL0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PdkL0.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 256) <= bv_unsigned a < (vz_2 - 256) + 4) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PdkL0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K14 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PdkL0.ps0) with 0x38c1c in Hms. change (SR.ps_regs PdkL0.ps0) with (map (fun i => (i, nth i PdkL0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PdkL0.ps0) with PdkL0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkL0.regs0 PdkL0.regs_out0 80 KS_dkL0 KS_dkL0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PdkL0.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PdkL0.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
  split. { rewrite (BG.out_reg PdkL0.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PdkL0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkL0.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PdkL0.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PdkL1 := LibSegBs_dkL1_u.
Definition KS_dkL1 : list nat := Eval vm_compute in (BG.kept_list 80 PdkL1.regs0 PdkL1.regs_out0).
Lemma KS_dkL1_ok : BG.kept_ok 80 PdkL1.regs0 PdkL1.regs_out0 KS_dkL1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dkL1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 5) = Z_to_bv 64 18446744073709551607 -> getr R (reg 6) = Z_to_bv 64 18446744073709551603 -> getr R (reg 7) = Z_to_bv 64 19342813113834067 -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 42) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + (V 38%nat)) -> getr R (reg 12) = Z_to_bv 64 (3 - (V 40%nat)) -> getr R (reg 13) = Z_to_bv 64 ((V 2%nat) - 240) -> getr R (reg 14) = Z_to_bv 64 (((V 2%nat) - 184) + (36 * (V 40%nat))) -> getr R (reg 15) = Z_to_bv 64 18446744073709551580 -> getr R (reg 16) = Z_to_bv 64 ((V 2%nat) - 216) -> getr R (reg 17) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 20) = Z_to_bv 64 (V 44%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 2%nat) - 252) -> getr R (reg 28) = Z_to_bv 64 1000000000 -> getr R (reg 29) = Z_to_bv 64 14757395259826634752 -> getr R (reg 30) = Z_to_bv 64 10 -> getr R (reg 31) = Z_to_bv 64 (V 40%nat) ->
  140735332483312 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) ->
  4096 <= (V 33%nat) <= 140737488355286 -> L5.writable RSEGS M (V 33%nat) 42 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 42 <= ((V 2%nat) - 256)) -> L5.img_clear M 65536 754672 ->
  0 <= (V 40%nat) <= 3 -> 0 <= (V 38%nat) <= 1 -> 0 <= (V 44%nat) <= 999999999 -> L5.u32_at RSEGS M ((V 2%nat) - 252) (V 45%nat) ->
  0 <= (V 45%nat) <= 4294967295 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 252) <= bv_unsigned a < ((V 2%nat) - 252) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 252) <= i < ((V 2%nat) - 252) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38c1c M) (st fx' R' 0x38c1c M')
        /\ (forall x, In x KS_dkL1 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 20)) = ((((4294967296 * (V 44%nat)) mod 2 ^ 64) + (((V 45%nat) + ((18446744072709551616 * ((((((((4294967296 * (V 44%nat)) mod 2 ^ 64) + (V 45%nat)) mod 2 ^ 64) / 512) * 19342813113834067) / 2 ^ 64) / 2048)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 2%nat) - 248)
        /\ bv_unsigned (getr R' (reg 22)) = ((1000000000 * ((((((((4294967296 * (V 44%nat)) mod 2 ^ 64) + (V 45%nat)) mod 2 ^ 64) / 512) * 19342813113834067) / 2 ^ 64) / 2048)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 252) ((((((((4294967296 * (V 44%nat)) mod 2 ^ 64) + (V 45%nat)) mod 2 ^ 64) / 512) * 19342813113834067) / 2 ^ 64) / 2048)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 G2 G5 G6 G7 G8 G9 G12 G13 G14 G15 G16 G17 G18 G20 G21 G28 G29 G30 G31 pvzI16 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 pvzI17 K13 K14 K15 pvzI18 pvzI19 pvzI20 K19 pvzI21.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV40l; move HV40l before pvzI4; pose proof (proj2 pvzI4) as HV40r; move HV40r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV44l; move HV44l before pvzI5; pose proof (proj2 pvzI5) as HV44r; move HV44r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV45l; move HV45l before pvzI6; pose proof (proj2 pvzI6) as HV45r; move HV45r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV60l; move HV60l before pvzI7; pose proof (proj2 pvzI7) as HV60r; move HV60r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV61l; move HV61l before pvzI8; pose proof (proj2 pvzI8) as HV61r; move HV61r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV62l; move HV62l before pvzI9; pose proof (proj2 pvzI9) as HV62r; move HV62r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV63l; move HV63l before pvzI10; pose proof (proj2 pvzI10) as HV63r; move HV63r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV64l; move HV64l before pvzI11; pose proof (proj2 pvzI11) as HV64r; move HV64r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV65l; move HV65l before pvzI12; pose proof (proj2 pvzI12) as HV65r; move HV65r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV66l; move HV66l before pvzI13; pose proof (proj2 pvzI13) as HV66r; move HV66r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV67l; move HV67l before pvzI14; pose proof (proj2 pvzI14) as HV67r; move HV67r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV68l; move HV68l before pvzI15; pose proof (proj2 pvzI15) as HV68r; move HV68r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K0l; move K0l before pvzI16; pose proof (proj2 pvzI16) as K0r; move K0r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K12l; move K12l before pvzI17; pose proof (proj2 pvzI17) as K12r; move K12r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K16l; move K16l before pvzI18; pose proof (proj2 pvzI18) as K16r; move K16r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K17l; move K17l before pvzI19; pose proof (proj2 pvzI19) as K17r; move K17r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K18l; move K18l before pvzI20; pose proof (proj2 pvzI20) as K18r; move K18r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K20l; move K20l before pvzI21; pose proof (proj2 pvzI21) as K20r; move K20r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 38%nat => Z_to_bv 64 vz_38 | 40%nat => Z_to_bv 64 vz_40 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 38%nat => vz_38 | 40%nat => vz_40 | 44%nat => vz_44 | 45%nat => vz_45 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 69%nat. }
  assert (HR: regs_ok E PdkL1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdkL1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdkL1.kn0).
  { unfold know_ok, PdkL1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV61l HV61r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV63l HV63r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K12l K12r K14; lia | clear - HV33l HV33r K12l K12r K14; lia | clear - HV33l HV33r K12l K12r K14; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV44l HV44r K18l K18r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV45l HV45r K20l K20r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PdkL1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PdkL1.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 252) <= bv_unsigned a < (vz_2 - 252) + 4) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PdkL1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K14 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PdkL1.ps0) with 0x38c1c in Hms. change (SR.ps_regs PdkL1.ps0) with (map (fun i => (i, nth i PdkL1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PdkL1.ps0) with PdkL1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkL1.regs0 PdkL1.regs_out0 80 KS_dkL1 KS_dkL1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PdkL1.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PdkL1.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
  split. { rewrite (BG.out_reg PdkL1.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PdkL1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkL1.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PdkL1.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PdkL2 := LibSegBs_dkL2_u.
Definition KS_dkL2 : list nat := Eval vm_compute in (BG.kept_list 80 PdkL2.regs0 PdkL2.regs_out0).
Lemma KS_dkL2_ok : BG.kept_ok 80 PdkL2.regs0 PdkL2.regs_out0 KS_dkL2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dkL2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 5) = Z_to_bv 64 18446744073709551607 -> getr R (reg 6) = Z_to_bv 64 18446744073709551603 -> getr R (reg 7) = Z_to_bv 64 19342813113834067 -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 42) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + (V 38%nat)) -> getr R (reg 12) = Z_to_bv 64 (3 - (V 40%nat)) -> getr R (reg 13) = Z_to_bv 64 ((V 2%nat) - 240) -> getr R (reg 14) = Z_to_bv 64 (((V 2%nat) - 184) + (36 * (V 40%nat))) -> getr R (reg 15) = Z_to_bv 64 18446744073709551580 -> getr R (reg 16) = Z_to_bv 64 ((V 2%nat) - 216) -> getr R (reg 17) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 20) = Z_to_bv 64 (V 44%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 2%nat) - 248) -> getr R (reg 28) = Z_to_bv 64 1000000000 -> getr R (reg 29) = Z_to_bv 64 14757395259826634752 -> getr R (reg 30) = Z_to_bv 64 10 -> getr R (reg 31) = Z_to_bv 64 (V 40%nat) ->
  140735332483312 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) ->
  4096 <= (V 33%nat) <= 140737488355286 -> L5.writable RSEGS M (V 33%nat) 42 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 42 <= ((V 2%nat) - 256)) -> L5.img_clear M 65536 754672 ->
  0 <= (V 40%nat) <= 3 -> 0 <= (V 38%nat) <= 1 -> 0 <= (V 44%nat) <= 999999999 -> L5.u32_at RSEGS M ((V 2%nat) - 248) (V 45%nat) ->
  0 <= (V 45%nat) <= 4294967295 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 248) <= bv_unsigned a < ((V 2%nat) - 248) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 248) <= i < ((V 2%nat) - 248) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38c1c M) (st fx' R' 0x38c1c M')
        /\ (forall x, In x KS_dkL2 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 20)) = ((((4294967296 * (V 44%nat)) mod 2 ^ 64) + (((V 45%nat) + ((18446744072709551616 * ((((((((4294967296 * (V 44%nat)) mod 2 ^ 64) + (V 45%nat)) mod 2 ^ 64) / 512) * 19342813113834067) / 2 ^ 64) / 2048)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 2%nat) - 244)
        /\ bv_unsigned (getr R' (reg 22)) = ((1000000000 * ((((((((4294967296 * (V 44%nat)) mod 2 ^ 64) + (V 45%nat)) mod 2 ^ 64) / 512) * 19342813113834067) / 2 ^ 64) / 2048)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 248) ((((((((4294967296 * (V 44%nat)) mod 2 ^ 64) + (V 45%nat)) mod 2 ^ 64) / 512) * 19342813113834067) / 2 ^ 64) / 2048)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 G2 G5 G6 G7 G8 G9 G12 G13 G14 G15 G16 G17 G18 G20 G21 G28 G29 G30 G31 pvzI16 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 pvzI17 K13 K14 K15 pvzI18 pvzI19 pvzI20 K19 pvzI21.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV40l; move HV40l before pvzI4; pose proof (proj2 pvzI4) as HV40r; move HV40r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV44l; move HV44l before pvzI5; pose proof (proj2 pvzI5) as HV44r; move HV44r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV45l; move HV45l before pvzI6; pose proof (proj2 pvzI6) as HV45r; move HV45r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV60l; move HV60l before pvzI7; pose proof (proj2 pvzI7) as HV60r; move HV60r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV61l; move HV61l before pvzI8; pose proof (proj2 pvzI8) as HV61r; move HV61r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV62l; move HV62l before pvzI9; pose proof (proj2 pvzI9) as HV62r; move HV62r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV63l; move HV63l before pvzI10; pose proof (proj2 pvzI10) as HV63r; move HV63r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV64l; move HV64l before pvzI11; pose proof (proj2 pvzI11) as HV64r; move HV64r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV65l; move HV65l before pvzI12; pose proof (proj2 pvzI12) as HV65r; move HV65r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV66l; move HV66l before pvzI13; pose proof (proj2 pvzI13) as HV66r; move HV66r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV67l; move HV67l before pvzI14; pose proof (proj2 pvzI14) as HV67r; move HV67r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV68l; move HV68l before pvzI15; pose proof (proj2 pvzI15) as HV68r; move HV68r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K0l; move K0l before pvzI16; pose proof (proj2 pvzI16) as K0r; move K0r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K12l; move K12l before pvzI17; pose proof (proj2 pvzI17) as K12r; move K12r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K16l; move K16l before pvzI18; pose proof (proj2 pvzI18) as K16r; move K16r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K17l; move K17l before pvzI19; pose proof (proj2 pvzI19) as K17r; move K17r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K18l; move K18l before pvzI20; pose proof (proj2 pvzI20) as K18r; move K18r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K20l; move K20l before pvzI21; pose proof (proj2 pvzI21) as K20r; move K20r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 38%nat => Z_to_bv 64 vz_38 | 40%nat => Z_to_bv 64 vz_40 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 38%nat => vz_38 | 40%nat => vz_40 | 44%nat => vz_44 | 45%nat => vz_45 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 69%nat. }
  assert (HR: regs_ok E PdkL2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdkL2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdkL2.kn0).
  { unfold know_ok, PdkL2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV61l HV61r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV63l HV63r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K12l K12r K14; lia | clear - HV33l HV33r K12l K12r K14; lia | clear - HV33l HV33r K12l K12r K14; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV44l HV44r K18l K18r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV45l HV45r K20l K20r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PdkL2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PdkL2.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 248) <= bv_unsigned a < (vz_2 - 248) + 4) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PdkL2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K14 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PdkL2.ps0) with 0x38c1c in Hms. change (SR.ps_regs PdkL2.ps0) with (map (fun i => (i, nth i PdkL2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PdkL2.ps0) with PdkL2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkL2.regs0 PdkL2.regs_out0 80 KS_dkL2 KS_dkL2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PdkL2.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PdkL2.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
  split. { rewrite (BG.out_reg PdkL2.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PdkL2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkL2.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PdkL2.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PdkL3 := LibSegBs_dkL3_u.
Definition KS_dkL3 : list nat := Eval vm_compute in (BG.kept_list 80 PdkL3.regs0 PdkL3.regs_out0).
Lemma KS_dkL3_ok : BG.kept_ok 80 PdkL3.regs0 PdkL3.regs_out0 KS_dkL3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dkL3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 5) = Z_to_bv 64 18446744073709551607 -> getr R (reg 6) = Z_to_bv 64 18446744073709551603 -> getr R (reg 7) = Z_to_bv 64 19342813113834067 -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 42) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + (V 38%nat)) -> getr R (reg 12) = Z_to_bv 64 (3 - (V 40%nat)) -> getr R (reg 13) = Z_to_bv 64 ((V 2%nat) - 240) -> getr R (reg 14) = Z_to_bv 64 (((V 2%nat) - 184) + (36 * (V 40%nat))) -> getr R (reg 15) = Z_to_bv 64 18446744073709551580 -> getr R (reg 16) = Z_to_bv 64 ((V 2%nat) - 216) -> getr R (reg 17) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 20) = Z_to_bv 64 (V 44%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 2%nat) - 244) -> getr R (reg 28) = Z_to_bv 64 1000000000 -> getr R (reg 29) = Z_to_bv 64 14757395259826634752 -> getr R (reg 30) = Z_to_bv 64 10 -> getr R (reg 31) = Z_to_bv 64 (V 40%nat) ->
  140735332483312 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) ->
  4096 <= (V 33%nat) <= 140737488355286 -> L5.writable RSEGS M (V 33%nat) 42 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 42 <= ((V 2%nat) - 256)) -> L5.img_clear M 65536 754672 ->
  0 <= (V 40%nat) <= 3 -> 0 <= (V 38%nat) <= 1 -> 0 <= (V 44%nat) <= 999999999 -> L5.u32_at RSEGS M ((V 2%nat) - 244) (V 45%nat) ->
  0 <= (V 45%nat) <= 4294967295 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 244) <= bv_unsigned a < ((V 2%nat) - 244) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 244) <= i < ((V 2%nat) - 244) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38c1c M) (st fx' R' 0x38c48 M')
        /\ (forall x, In x KS_dkL3 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 20)) = ((((4294967296 * (V 44%nat)) mod 2 ^ 64) + (((V 45%nat) + ((18446744072709551616 * ((((((((4294967296 * (V 44%nat)) mod 2 ^ 64) + (V 45%nat)) mod 2 ^ 64) / 512) * 19342813113834067) / 2 ^ 64) / 2048)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 2%nat) - 240)
        /\ bv_unsigned (getr R' (reg 22)) = ((1000000000 * ((((((((4294967296 * (V 44%nat)) mod 2 ^ 64) + (V 45%nat)) mod 2 ^ 64) / 512) * 19342813113834067) / 2 ^ 64) / 2048)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 244) ((((((((4294967296 * (V 44%nat)) mod 2 ^ 64) + (V 45%nat)) mod 2 ^ 64) / 512) * 19342813113834067) / 2 ^ 64) / 2048)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 G2 G5 G6 G7 G8 G9 G12 G13 G14 G15 G16 G17 G18 G20 G21 G28 G29 G30 G31 pvzI16 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 pvzI17 K13 K14 K15 pvzI18 pvzI19 pvzI20 K19 pvzI21.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV40l; move HV40l before pvzI4; pose proof (proj2 pvzI4) as HV40r; move HV40r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV44l; move HV44l before pvzI5; pose proof (proj2 pvzI5) as HV44r; move HV44r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV45l; move HV45l before pvzI6; pose proof (proj2 pvzI6) as HV45r; move HV45r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV60l; move HV60l before pvzI7; pose proof (proj2 pvzI7) as HV60r; move HV60r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV61l; move HV61l before pvzI8; pose proof (proj2 pvzI8) as HV61r; move HV61r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV62l; move HV62l before pvzI9; pose proof (proj2 pvzI9) as HV62r; move HV62r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV63l; move HV63l before pvzI10; pose proof (proj2 pvzI10) as HV63r; move HV63r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV64l; move HV64l before pvzI11; pose proof (proj2 pvzI11) as HV64r; move HV64r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV65l; move HV65l before pvzI12; pose proof (proj2 pvzI12) as HV65r; move HV65r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV66l; move HV66l before pvzI13; pose proof (proj2 pvzI13) as HV66r; move HV66r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV67l; move HV67l before pvzI14; pose proof (proj2 pvzI14) as HV67r; move HV67r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV68l; move HV68l before pvzI15; pose proof (proj2 pvzI15) as HV68r; move HV68r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K0l; move K0l before pvzI16; pose proof (proj2 pvzI16) as K0r; move K0r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K12l; move K12l before pvzI17; pose proof (proj2 pvzI17) as K12r; move K12r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K16l; move K16l before pvzI18; pose proof (proj2 pvzI18) as K16r; move K16r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K17l; move K17l before pvzI19; pose proof (proj2 pvzI19) as K17r; move K17r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K18l; move K18l before pvzI20; pose proof (proj2 pvzI20) as K18r; move K18r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K20l; move K20l before pvzI21; pose proof (proj2 pvzI21) as K20r; move K20r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 38%nat => Z_to_bv 64 vz_38 | 40%nat => Z_to_bv 64 vz_40 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 38%nat => vz_38 | 40%nat => vz_40 | 44%nat => vz_44 | 45%nat => vz_45 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 69%nat. }
  assert (HR: regs_ok E PdkL3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdkL3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdkL3.kn0).
  { unfold know_ok, PdkL3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV61l HV61r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV63l HV63r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K12l K12r K14; lia | clear - HV33l HV33r K12l K12r K14; lia | clear - HV33l HV33r K12l K12r K14; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV44l HV44r K18l K18r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV45l HV45r K20l K20r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PdkL3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PdkL3.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 244) <= bv_unsigned a < (vz_2 - 244) + 4) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PdkL3.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K14 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PdkL3.ps0) with 0x38c48 in Hms. change (SR.ps_regs PdkL3.ps0) with (map (fun i => (i, nth i PdkL3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PdkL3.ps0) with PdkL3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkL3.regs0 PdkL3.regs_out0 80 KS_dkL3 KS_dkL3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PdkL3.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PdkL3.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
  split. { rewrite (BG.out_reg PdkL3.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PdkL3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkL3.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PdkL3.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PdkRM := LibSegBs_dkRM_u.
Definition KS_dkRM_0 : list nat := Eval vm_compute in (BG.kept_list 80 PdkRM.regs0 PdkRM.regs_out0).
Lemma KS_dkRM_0_ok : BG.kept_ok 80 PdkRM.regs0 PdkRM.regs_out0 KS_dkRM_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_dkRM_1 : list nat := Eval vm_compute in (BG.kept_list 80 PdkRM.regs0 PdkRM.regs_out1).
Lemma KS_dkRM_1_ok : BG.kept_ok 80 PdkRM.regs0 PdkRM.regs_out1 KS_dkRM_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dkRM_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 5) = Z_to_bv 64 18446744073709551607 -> getr R (reg 6) = Z_to_bv 64 18446744073709551603 -> getr R (reg 7) = Z_to_bv 64 19342813113834067 -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 42) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + (V 38%nat)) -> getr R (reg 12) = Z_to_bv 64 (3 - (V 40%nat)) -> getr R (reg 13) = Z_to_bv 64 ((V 2%nat) - 240) -> getr R (reg 14) = Z_to_bv 64 (((V 2%nat) - 184) + (36 * (V 40%nat))) -> getr R (reg 15) = Z_to_bv 64 18446744073709551580 -> getr R (reg 16) = Z_to_bv 64 ((V 2%nat) - 216) -> getr R (reg 17) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 20) = Z_to_bv 64 (V 48%nat) -> getr R (reg 28) = Z_to_bv 64 1000000000 -> getr R (reg 29) = Z_to_bv 64 14757395259826634752 -> getr R (reg 30) = Z_to_bv 64 10 -> getr R (reg 31) = Z_to_bv 64 (V 40%nat) ->
  140735332483312 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) ->
  4096 <= (V 33%nat) <= 140737488355286 -> L5.writable RSEGS M (V 33%nat) 42 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 42 <= ((V 2%nat) - 256)) -> L5.img_clear M 65536 754672 ->
  0 <= (V 40%nat) <= 3 -> 0 <= (V 38%nat) <= 1 -> 0 <= (V 48%nat) <= 999999999 -> L5.u64_at RSEGS M ((V 2%nat) - 256) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 248) (V 47%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 232) <= bv_unsigned a < ((V 2%nat) - 232) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 232) <= i < ((V 2%nat) - 232) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x38c48 M) (st fx' R' 0x38c84 M')
        /\ (forall x, In x KS_dkRM_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 21) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 47%nat)
        /\ (((V 48%nat) - 0) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) (V 46%nat))
      \/ (msteps RSEGS (st fx R 0x38c48 M) (st fx' R' 0x38c60 M')
        /\ (forall x, In x KS_dkRM_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 21) = Z_to_bv 64 (((V 2%nat) + (36 * (V 40%nat))) - 184)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 47%nat)
        /\ 1 <= (((V 48%nat) - 0) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) (V 46%nat))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 G2 G5 G6 G7 G8 G9 G12 G13 G14 G15 G16 G17 G18 G20 G28 G29 G30 G31 pvzI17 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 pvzI18 K13 K14 K15 pvzI19 pvzI20 pvzI21 K19 K20.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV40l; move HV40l before pvzI4; pose proof (proj2 pvzI4) as HV40r; move HV40r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV46l; move HV46l before pvzI5; pose proof (proj2 pvzI5) as HV46r; move HV46r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV47l; move HV47l before pvzI6; pose proof (proj2 pvzI6) as HV47r; move HV47r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV48l; move HV48l before pvzI7; pose proof (proj2 pvzI7) as HV48r; move HV48r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV60l; move HV60l before pvzI8; pose proof (proj2 pvzI8) as HV60r; move HV60r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV61l; move HV61l before pvzI9; pose proof (proj2 pvzI9) as HV61r; move HV61r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV62l; move HV62l before pvzI10; pose proof (proj2 pvzI10) as HV62r; move HV62r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV63l; move HV63l before pvzI11; pose proof (proj2 pvzI11) as HV63r; move HV63r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV64l; move HV64l before pvzI12; pose proof (proj2 pvzI12) as HV64r; move HV64r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV65l; move HV65l before pvzI13; pose proof (proj2 pvzI13) as HV65r; move HV65r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV66l; move HV66l before pvzI14; pose proof (proj2 pvzI14) as HV66r; move HV66r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV67l; move HV67l before pvzI15; pose proof (proj2 pvzI15) as HV67r; move HV67r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV68l; move HV68l before pvzI16; pose proof (proj2 pvzI16) as HV68r; move HV68r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K0l; move K0l before pvzI17; pose proof (proj2 pvzI17) as K0r; move K0r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K12l; move K12l before pvzI18; pose proof (proj2 pvzI18) as K12r; move K12r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K16l; move K16l before pvzI19; pose proof (proj2 pvzI19) as K16r; move K16r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K17l; move K17l before pvzI20; pose proof (proj2 pvzI20) as K17r; move K17r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K18l; move K18l before pvzI21; pose proof (proj2 pvzI21) as K18r; move K18r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 38%nat => Z_to_bv 64 vz_38 | 40%nat => Z_to_bv 64 vz_40 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 38%nat => vz_38 | 40%nat => vz_40 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 69%nat. }
  assert (HR: regs_ok E PdkRM.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdkRM.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdkRM.kn0).
  { unfold know_ok, PdkRM.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV61l HV61r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV63l HV63r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K12l K12r K14; lia | clear - HV33l HV33r K12l K12r K14; lia | clear - HV33l HV33r K12l K12r K14; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K18l K18r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K20]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PdkRM.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PdkRM.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 232) <= bv_unsigned a < (vz_2 - 232) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PdkRM.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K14 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PdkRM.ps0) with 0x38c84 in Hms. change (SR.ps_regs PdkRM.ps0) with (map (fun i => (i, nth i PdkRM.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PdkRM.ps0) with PdkRM.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkRM.regs0 PdkRM.regs_out0 80 KS_dkRM_0 KS_dkRM_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PdkRM.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PdkRM.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkRM.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PdkRM.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk' ZA Hag ltac:(clear - HV47l HV47r) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. 
  - right.
    change (SR.ps_pc PdkRM.ps1) with 0x38c60 in Hms. change (SR.ps_regs PdkRM.ps1) with (map (fun i => (i, nth i PdkRM.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PdkRM.ps1) with PdkRM.cells1 in Hcells. unfold PdkRM.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkRM.regs0 PdkRM.regs_out1 80 KS_dkRM_1 KS_dkRM_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PdkRM.regs_out1 E' R' 21 Hregs) by (clear; lia). cbn [nth PdkRM.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkRM.regs_out1 E' R' 22 Hregs) by (clear; lia). cbn [nth PdkRM.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk' ZA Hag ltac:(clear - HV47l HV47r) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PdkRD0 := LibSegBs_dkRD0_u.
Definition KS_dkRD0 : list nat := Eval vm_compute in (BG.kept_list 80 PdkRD0.regs0 PdkRD0.regs_out0).
Lemma KS_dkRD0_ok : BG.kept_ok 80 PdkRD0.regs0 PdkRD0.regs_out0 KS_dkRD0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dkRD0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 5) = Z_to_bv 64 18446744073709551607 -> getr R (reg 6) = Z_to_bv 64 18446744073709551603 -> getr R (reg 7) = Z_to_bv 64 19342813113834067 -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 42) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + (V 38%nat)) -> getr R (reg 12) = Z_to_bv 64 3 -> getr R (reg 13) = Z_to_bv 64 ((V 2%nat) - 240) -> getr R (reg 14) = Z_to_bv 64 ((V 2%nat) - 184) -> getr R (reg 15) = Z_to_bv 64 18446744073709551580 -> getr R (reg 16) = Z_to_bv 64 ((V 2%nat) - 216) -> getr R (reg 17) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 2%nat) - 220) -> getr R (reg 20) = Z_to_bv 64 (V 48%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 2%nat) - 184) -> getr R (reg 28) = Z_to_bv 64 1000000000 -> getr R (reg 29) = Z_to_bv 64 14757395259826634752 -> getr R (reg 30) = Z_to_bv 64 10 -> getr R (reg 31) = Z_to_bv 64 0 ->
  140735332483312 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) ->
  4096 <= (V 33%nat) <= 140737488355286 -> L5.writable RSEGS M (V 33%nat) 42 -> (((V 2%nat) - 18432) + 18432 <= (V 33%nat) \/ (V 33%nat) + 42 <= ((V 2%nat) - 18432)) -> L5.img_clear M 65536 754672 ->
  0 <= (V 38%nat) <= 1 -> 1 <= (V 48%nat) <= 999999999 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 216) <= bv_unsigned a < ((V 2%nat) - 216) + 36) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 216) <= i < ((V 2%nat) - 216) + 36) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38c60 M) (st fx' R' 0x38c84 M')
        /\ (forall x, In x KS_dkRD0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 20) = Z_to_bv 64 0
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 2%nat) - 220)
        /\ getr R' (reg 22) = Z_to_bv 64 0
        /\ getr R' (reg 23) = Z_to_bv 64 0
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 216) (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 212) (((((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 208) (((((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 204) (((((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 200) (((((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 196) (((((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 192) (((((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 188) (((((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 184) (((V 48%nat) + ((18446744073709551606 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 G2 G5 G6 G7 G8 G9 G12 G13 G14 G15 G16 G17 G18 G19 G20 G21 G28 G29 G30 G31 pvzI14 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 pvzI15 K13 K14 K15 pvzI16 pvzI17.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV48l; move HV48l before pvzI4; pose proof (proj2 pvzI4) as HV48r; move HV48r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV60l; move HV60l before pvzI5; pose proof (proj2 pvzI5) as HV60r; move HV60r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV61l; move HV61l before pvzI6; pose proof (proj2 pvzI6) as HV61r; move HV61r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV62l; move HV62l before pvzI7; pose proof (proj2 pvzI7) as HV62r; move HV62r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV63l; move HV63l before pvzI8; pose proof (proj2 pvzI8) as HV63r; move HV63r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV64l; move HV64l before pvzI9; pose proof (proj2 pvzI9) as HV64r; move HV64r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV65l; move HV65l before pvzI10; pose proof (proj2 pvzI10) as HV65r; move HV65r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV66l; move HV66l before pvzI11; pose proof (proj2 pvzI11) as HV66r; move HV66r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV67l; move HV67l before pvzI12; pose proof (proj2 pvzI12) as HV67r; move HV67r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV68l; move HV68l before pvzI13; pose proof (proj2 pvzI13) as HV68r; move HV68r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K0l; move K0l before pvzI14; pose proof (proj2 pvzI14) as K0r; move K0r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K12l; move K12l before pvzI15; pose proof (proj2 pvzI15) as K12r; move K12r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K16l; move K16l before pvzI16; pose proof (proj2 pvzI16) as K16r; move K16r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K17l; move K17l before pvzI17; pose proof (proj2 pvzI17) as K17r; move K17r before pvzI17; clear pvzI17.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 38%nat => Z_to_bv 64 vz_38 | 48%nat => Z_to_bv 64 vz_48 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 38%nat => vz_38 | 48%nat => vz_48 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 69%nat. }
  assert (HR: regs_ok E PdkRD0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdkRD0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdkRD0.kn0).
  { unfold know_ok, PdkRD0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV61l HV61r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV63l HV63r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K12l K12r K14; lia | clear - HV33l HV33r K12l K12r K14; lia | clear - HV33l HV33r K12l K12r K14; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PdkRD0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PdkRD0.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 216) <= bv_unsigned a < (vz_2 - 216) + 36) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PdkRD0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K14 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PdkRD0.ps0) with 0x38c84 in Hms. change (SR.ps_regs PdkRD0.ps0) with (map (fun i => (i, nth i PdkRD0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PdkRD0.ps0) with PdkRD0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkRD0.regs0 PdkRD0.regs_out0 80 KS_dkRD0 KS_dkRD0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PdkRD0.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PdkRD0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkRD0.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PdkRD0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkRD0.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PdkRD0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkRD0.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PdkRD0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 3); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 4); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 5); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 6); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 7); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 8); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PdkRD1 := LibSegBs_dkRD1_u.
Definition KS_dkRD1 : list nat := Eval vm_compute in (BG.kept_list 80 PdkRD1.regs0 PdkRD1.regs_out0).
Lemma KS_dkRD1_ok : BG.kept_ok 80 PdkRD1.regs0 PdkRD1.regs_out0 KS_dkRD1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dkRD1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 5) = Z_to_bv 64 18446744073709551607 -> getr R (reg 6) = Z_to_bv 64 18446744073709551603 -> getr R (reg 7) = Z_to_bv 64 19342813113834067 -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 42) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + (V 38%nat)) -> getr R (reg 12) = Z_to_bv 64 2 -> getr R (reg 13) = Z_to_bv 64 ((V 2%nat) - 240) -> getr R (reg 14) = Z_to_bv 64 ((V 2%nat) - 148) -> getr R (reg 15) = Z_to_bv 64 18446744073709551580 -> getr R (reg 16) = Z_to_bv 64 ((V 2%nat) - 216) -> getr R (reg 17) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 2%nat) - 184) -> getr R (reg 20) = Z_to_bv 64 (V 48%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 2%nat) - 148) -> getr R (reg 28) = Z_to_bv 64 1000000000 -> getr R (reg 29) = Z_to_bv 64 14757395259826634752 -> getr R (reg 30) = Z_to_bv 64 10 -> getr R (reg 31) = Z_to_bv 64 1 ->
  140735332483312 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) ->
  4096 <= (V 33%nat) <= 140737488355286 -> L5.writable RSEGS M (V 33%nat) 42 -> (((V 2%nat) - 18432) + 18432 <= (V 33%nat) \/ (V 33%nat) + 42 <= ((V 2%nat) - 18432)) -> L5.img_clear M 65536 754672 ->
  0 <= (V 38%nat) <= 1 -> 1 <= (V 48%nat) <= 999999999 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 180) <= bv_unsigned a < ((V 2%nat) - 180) + 36) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 180) <= i < ((V 2%nat) - 180) + 36) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38c60 M) (st fx' R' 0x38c84 M')
        /\ (forall x, In x KS_dkRD1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 20) = Z_to_bv 64 0
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 2%nat) - 184)
        /\ getr R' (reg 22) = Z_to_bv 64 0
        /\ getr R' (reg 23) = Z_to_bv 64 0
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 180) (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 176) (((((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 172) (((((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 168) (((((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 164) (((((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 160) (((((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 156) (((((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 152) (((((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 148) (((V 48%nat) + ((18446744073709551606 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 G2 G5 G6 G7 G8 G9 G12 G13 G14 G15 G16 G17 G18 G19 G20 G21 G28 G29 G30 G31 pvzI14 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 pvzI15 K13 K14 K15 pvzI16 pvzI17.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV48l; move HV48l before pvzI4; pose proof (proj2 pvzI4) as HV48r; move HV48r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV60l; move HV60l before pvzI5; pose proof (proj2 pvzI5) as HV60r; move HV60r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV61l; move HV61l before pvzI6; pose proof (proj2 pvzI6) as HV61r; move HV61r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV62l; move HV62l before pvzI7; pose proof (proj2 pvzI7) as HV62r; move HV62r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV63l; move HV63l before pvzI8; pose proof (proj2 pvzI8) as HV63r; move HV63r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV64l; move HV64l before pvzI9; pose proof (proj2 pvzI9) as HV64r; move HV64r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV65l; move HV65l before pvzI10; pose proof (proj2 pvzI10) as HV65r; move HV65r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV66l; move HV66l before pvzI11; pose proof (proj2 pvzI11) as HV66r; move HV66r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV67l; move HV67l before pvzI12; pose proof (proj2 pvzI12) as HV67r; move HV67r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV68l; move HV68l before pvzI13; pose proof (proj2 pvzI13) as HV68r; move HV68r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K0l; move K0l before pvzI14; pose proof (proj2 pvzI14) as K0r; move K0r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K12l; move K12l before pvzI15; pose proof (proj2 pvzI15) as K12r; move K12r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K16l; move K16l before pvzI16; pose proof (proj2 pvzI16) as K16r; move K16r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K17l; move K17l before pvzI17; pose proof (proj2 pvzI17) as K17r; move K17r before pvzI17; clear pvzI17.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 38%nat => Z_to_bv 64 vz_38 | 48%nat => Z_to_bv 64 vz_48 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 38%nat => vz_38 | 48%nat => vz_48 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 69%nat. }
  assert (HR: regs_ok E PdkRD1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdkRD1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdkRD1.kn0).
  { unfold know_ok, PdkRD1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV61l HV61r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV63l HV63r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K12l K12r K14; lia | clear - HV33l HV33r K12l K12r K14; lia | clear - HV33l HV33r K12l K12r K14; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PdkRD1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PdkRD1.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 180) <= bv_unsigned a < (vz_2 - 180) + 36) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PdkRD1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K14 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PdkRD1.ps0) with 0x38c84 in Hms. change (SR.ps_regs PdkRD1.ps0) with (map (fun i => (i, nth i PdkRD1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PdkRD1.ps0) with PdkRD1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkRD1.regs0 PdkRD1.regs_out0 80 KS_dkRD1 KS_dkRD1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PdkRD1.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PdkRD1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkRD1.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PdkRD1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkRD1.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PdkRD1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkRD1.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PdkRD1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 3); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 4); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 5); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 6); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 7); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 8); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PdkRD2 := LibSegBs_dkRD2_u.
Definition KS_dkRD2 : list nat := Eval vm_compute in (BG.kept_list 80 PdkRD2.regs0 PdkRD2.regs_out0).
Lemma KS_dkRD2_ok : BG.kept_ok 80 PdkRD2.regs0 PdkRD2.regs_out0 KS_dkRD2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dkRD2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 5) = Z_to_bv 64 18446744073709551607 -> getr R (reg 6) = Z_to_bv 64 18446744073709551603 -> getr R (reg 7) = Z_to_bv 64 19342813113834067 -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 42) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + (V 38%nat)) -> getr R (reg 12) = Z_to_bv 64 1 -> getr R (reg 13) = Z_to_bv 64 ((V 2%nat) - 240) -> getr R (reg 14) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 15) = Z_to_bv 64 18446744073709551580 -> getr R (reg 16) = Z_to_bv 64 ((V 2%nat) - 216) -> getr R (reg 17) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 2%nat) - 148) -> getr R (reg 20) = Z_to_bv 64 (V 48%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 28) = Z_to_bv 64 1000000000 -> getr R (reg 29) = Z_to_bv 64 14757395259826634752 -> getr R (reg 30) = Z_to_bv 64 10 -> getr R (reg 31) = Z_to_bv 64 2 ->
  140735332483312 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) ->
  4096 <= (V 33%nat) <= 140737488355286 -> L5.writable RSEGS M (V 33%nat) 42 -> (((V 2%nat) - 18432) + 18432 <= (V 33%nat) \/ (V 33%nat) + 42 <= ((V 2%nat) - 18432)) -> L5.img_clear M 65536 754672 ->
  0 <= (V 38%nat) <= 1 -> 1 <= (V 48%nat) <= 999999999 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 144) <= bv_unsigned a < ((V 2%nat) - 144) + 36) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 144) <= i < ((V 2%nat) - 144) + 36) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38c60 M) (st fx' R' 0x38c84 M')
        /\ (forall x, In x KS_dkRD2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 20) = Z_to_bv 64 0
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 2%nat) - 148)
        /\ getr R' (reg 22) = Z_to_bv 64 0
        /\ getr R' (reg 23) = Z_to_bv 64 0
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 144) (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 140) (((((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 136) (((((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 132) (((((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 128) (((((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 124) (((((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 120) (((((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 116) (((((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 112) (((V 48%nat) + ((18446744073709551606 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 G2 G5 G6 G7 G8 G9 G12 G13 G14 G15 G16 G17 G18 G19 G20 G21 G28 G29 G30 G31 pvzI14 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 pvzI15 K13 K14 K15 pvzI16 pvzI17.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV48l; move HV48l before pvzI4; pose proof (proj2 pvzI4) as HV48r; move HV48r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV60l; move HV60l before pvzI5; pose proof (proj2 pvzI5) as HV60r; move HV60r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV61l; move HV61l before pvzI6; pose proof (proj2 pvzI6) as HV61r; move HV61r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV62l; move HV62l before pvzI7; pose proof (proj2 pvzI7) as HV62r; move HV62r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV63l; move HV63l before pvzI8; pose proof (proj2 pvzI8) as HV63r; move HV63r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV64l; move HV64l before pvzI9; pose proof (proj2 pvzI9) as HV64r; move HV64r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV65l; move HV65l before pvzI10; pose proof (proj2 pvzI10) as HV65r; move HV65r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV66l; move HV66l before pvzI11; pose proof (proj2 pvzI11) as HV66r; move HV66r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV67l; move HV67l before pvzI12; pose proof (proj2 pvzI12) as HV67r; move HV67r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV68l; move HV68l before pvzI13; pose proof (proj2 pvzI13) as HV68r; move HV68r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K0l; move K0l before pvzI14; pose proof (proj2 pvzI14) as K0r; move K0r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K12l; move K12l before pvzI15; pose proof (proj2 pvzI15) as K12r; move K12r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K16l; move K16l before pvzI16; pose proof (proj2 pvzI16) as K16r; move K16r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K17l; move K17l before pvzI17; pose proof (proj2 pvzI17) as K17r; move K17r before pvzI17; clear pvzI17.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 38%nat => Z_to_bv 64 vz_38 | 48%nat => Z_to_bv 64 vz_48 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 38%nat => vz_38 | 48%nat => vz_48 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 69%nat. }
  assert (HR: regs_ok E PdkRD2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdkRD2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdkRD2.kn0).
  { unfold know_ok, PdkRD2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV61l HV61r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV63l HV63r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K12l K12r K14; lia | clear - HV33l HV33r K12l K12r K14; lia | clear - HV33l HV33r K12l K12r K14; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PdkRD2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PdkRD2.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 144) <= bv_unsigned a < (vz_2 - 144) + 36) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PdkRD2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K14 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PdkRD2.ps0) with 0x38c84 in Hms. change (SR.ps_regs PdkRD2.ps0) with (map (fun i => (i, nth i PdkRD2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PdkRD2.ps0) with PdkRD2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkRD2.regs0 PdkRD2.regs_out0 80 KS_dkRD2 KS_dkRD2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PdkRD2.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PdkRD2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkRD2.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PdkRD2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkRD2.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PdkRD2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkRD2.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PdkRD2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 3); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 4); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 5); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 6); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 7); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 8); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PdkRD3 := LibSegBs_dkRD3_u.
Definition KS_dkRD3 : list nat := Eval vm_compute in (BG.kept_list 80 PdkRD3.regs0 PdkRD3.regs_out0).
Lemma KS_dkRD3_ok : BG.kept_ok 80 PdkRD3.regs0 PdkRD3.regs_out0 KS_dkRD3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dkRD3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 5) = Z_to_bv 64 18446744073709551607 -> getr R (reg 6) = Z_to_bv 64 18446744073709551603 -> getr R (reg 7) = Z_to_bv 64 19342813113834067 -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 42) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + (V 38%nat)) -> getr R (reg 12) = Z_to_bv 64 0 -> getr R (reg 13) = Z_to_bv 64 ((V 2%nat) - 240) -> getr R (reg 14) = Z_to_bv 64 ((V 2%nat) - 76) -> getr R (reg 15) = Z_to_bv 64 18446744073709551580 -> getr R (reg 16) = Z_to_bv 64 ((V 2%nat) - 216) -> getr R (reg 17) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 20) = Z_to_bv 64 (V 48%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 2%nat) - 76) -> getr R (reg 28) = Z_to_bv 64 1000000000 -> getr R (reg 29) = Z_to_bv 64 14757395259826634752 -> getr R (reg 30) = Z_to_bv 64 10 -> getr R (reg 31) = Z_to_bv 64 3 ->
  140735332483312 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) ->
  4096 <= (V 33%nat) <= 140737488355286 -> L5.writable RSEGS M (V 33%nat) 42 -> (((V 2%nat) - 18432) + 18432 <= (V 33%nat) \/ (V 33%nat) + 42 <= ((V 2%nat) - 18432)) -> L5.img_clear M 65536 754672 ->
  0 <= (V 38%nat) <= 1 -> 1 <= (V 48%nat) <= 999999999 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 108) <= bv_unsigned a < ((V 2%nat) - 108) + 36) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 108) <= i < ((V 2%nat) - 108) + 36) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38c60 M) (st fx' R' 0x38c84 M')
        /\ (forall x, In x KS_dkRD3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 20) = Z_to_bv 64 0
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 2%nat) - 112)
        /\ getr R' (reg 22) = Z_to_bv 64 0
        /\ getr R' (reg 23) = Z_to_bv 64 0
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 108) (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 104) (((((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 100) (((((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 96) (((((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 92) (((((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 88) (((((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 84) (((((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 80) (((((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) + ((18446744073709551606 * (((((4294967296 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 76) (((V 48%nat) + ((18446744073709551606 * (((((4294967296 * (V 48%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 G2 G5 G6 G7 G8 G9 G12 G13 G14 G15 G16 G17 G18 G19 G20 G21 G28 G29 G30 G31 pvzI14 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 pvzI15 K13 K14 K15 pvzI16 pvzI17.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV48l; move HV48l before pvzI4; pose proof (proj2 pvzI4) as HV48r; move HV48r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV60l; move HV60l before pvzI5; pose proof (proj2 pvzI5) as HV60r; move HV60r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV61l; move HV61l before pvzI6; pose proof (proj2 pvzI6) as HV61r; move HV61r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV62l; move HV62l before pvzI7; pose proof (proj2 pvzI7) as HV62r; move HV62r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV63l; move HV63l before pvzI8; pose proof (proj2 pvzI8) as HV63r; move HV63r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV64l; move HV64l before pvzI9; pose proof (proj2 pvzI9) as HV64r; move HV64r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV65l; move HV65l before pvzI10; pose proof (proj2 pvzI10) as HV65r; move HV65r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV66l; move HV66l before pvzI11; pose proof (proj2 pvzI11) as HV66r; move HV66r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV67l; move HV67l before pvzI12; pose proof (proj2 pvzI12) as HV67r; move HV67r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV68l; move HV68l before pvzI13; pose proof (proj2 pvzI13) as HV68r; move HV68r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K0l; move K0l before pvzI14; pose proof (proj2 pvzI14) as K0r; move K0r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K12l; move K12l before pvzI15; pose proof (proj2 pvzI15) as K12r; move K12r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K16l; move K16l before pvzI16; pose proof (proj2 pvzI16) as K16r; move K16r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K17l; move K17l before pvzI17; pose proof (proj2 pvzI17) as K17r; move K17r before pvzI17; clear pvzI17.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 38%nat => Z_to_bv 64 vz_38 | 48%nat => Z_to_bv 64 vz_48 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 38%nat => vz_38 | 48%nat => vz_48 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 69%nat. }
  assert (HR: regs_ok E PdkRD3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdkRD3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdkRD3.kn0).
  { unfold know_ok, PdkRD3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV61l HV61r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV63l HV63r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K12l K12r K14; lia | clear - HV33l HV33r K12l K12r K14; lia | clear - HV33l HV33r K12l K12r K14; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PdkRD3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PdkRD3.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 108) <= bv_unsigned a < (vz_2 - 108) + 36) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PdkRD3.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K14 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PdkRD3.ps0) with 0x38c84 in Hms. change (SR.ps_regs PdkRD3.ps0) with (map (fun i => (i, nth i PdkRD3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PdkRD3.ps0) with PdkRD3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkRD3.regs0 PdkRD3.regs_out0 80 KS_dkRD3 KS_dkRD3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PdkRD3.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PdkRD3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkRD3.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PdkRD3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkRD3.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PdkRD3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkRD3.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PdkRD3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 3); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 4); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 5); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 6); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 7); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 8); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PdkRT := LibSegBs_dkRT_u.
Definition KS_dkRT_0 : list nat := Eval vm_compute in (BG.kept_list 80 PdkRT.regs0 PdkRT.regs_out0).
Lemma KS_dkRT_0_ok : BG.kept_ok 80 PdkRT.regs0 PdkRT.regs_out0 KS_dkRT_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_dkRT_1 : list nat := Eval vm_compute in (BG.kept_list 80 PdkRT.regs0 PdkRT.regs_out1).
Lemma KS_dkRT_1_ok : BG.kept_ok 80 PdkRT.regs0 PdkRT.regs_out1 KS_dkRT_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dkRT_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 5) = Z_to_bv 64 18446744073709551607 -> getr R (reg 6) = Z_to_bv 64 18446744073709551603 -> getr R (reg 7) = Z_to_bv 64 19342813113834067 -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 42) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + (V 38%nat)) -> getr R (reg 12) = Z_to_bv 64 (3 - (V 40%nat)) -> getr R (reg 13) = Z_to_bv 64 ((V 2%nat) - 240) -> getr R (reg 14) = Z_to_bv 64 (((V 2%nat) - 184) + (36 * (V 40%nat))) -> getr R (reg 15) = Z_to_bv 64 18446744073709551580 -> getr R (reg 16) = Z_to_bv 64 ((V 2%nat) - 216) -> getr R (reg 17) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 28) = Z_to_bv 64 1000000000 -> getr R (reg 29) = Z_to_bv 64 14757395259826634752 -> getr R (reg 30) = Z_to_bv 64 10 -> getr R (reg 31) = Z_to_bv 64 (V 40%nat) ->
  140735332483312 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) ->
  4096 <= (V 33%nat) <= 140737488355286 -> L5.writable RSEGS M (V 33%nat) 42 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 42 <= ((V 2%nat) - 256)) -> L5.img_clear M 65536 754672 ->
  0 <= (V 40%nat) <= 3 -> 0 <= (V 38%nat) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x38c84 M) (st fx' R' 0x38c94 M')
        /\ (forall x, In x KS_dkRT_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 12) = Z_to_bv 64 (((-1) * (V 40%nat)) + 4)
        /\ getr R' (reg 14) = Z_to_bv 64 (((V 2%nat) + (36 * (V 40%nat))) - 220)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 40%nat) - 1)
        /\ (((V 40%nat) - 0) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0x38c84 M) (st fx' R' 0x38bc4 M')
        /\ (forall x, In x KS_dkRT_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 12) = Z_to_bv 64 (((-1) * (V 40%nat)) + 4)
        /\ getr R' (reg 14) = Z_to_bv 64 (((V 2%nat) + (36 * (V 40%nat))) - 220)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 40%nat) - 1)
        /\ 1 <= (((V 40%nat) - 0) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 G2 G5 G6 G7 G8 G9 G12 G13 G14 G15 G16 G17 G18 G28 G29 G30 G31 pvzI14 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 pvzI15 K13 K14 K15 pvzI16 pvzI17.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV40l; move HV40l before pvzI4; pose proof (proj2 pvzI4) as HV40r; move HV40r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV60l; move HV60l before pvzI5; pose proof (proj2 pvzI5) as HV60r; move HV60r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV61l; move HV61l before pvzI6; pose proof (proj2 pvzI6) as HV61r; move HV61r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV62l; move HV62l before pvzI7; pose proof (proj2 pvzI7) as HV62r; move HV62r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV63l; move HV63l before pvzI8; pose proof (proj2 pvzI8) as HV63r; move HV63r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV64l; move HV64l before pvzI9; pose proof (proj2 pvzI9) as HV64r; move HV64r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV65l; move HV65l before pvzI10; pose proof (proj2 pvzI10) as HV65r; move HV65r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV66l; move HV66l before pvzI11; pose proof (proj2 pvzI11) as HV66r; move HV66r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV67l; move HV67l before pvzI12; pose proof (proj2 pvzI12) as HV67r; move HV67r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV68l; move HV68l before pvzI13; pose proof (proj2 pvzI13) as HV68r; move HV68r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K0l; move K0l before pvzI14; pose proof (proj2 pvzI14) as K0r; move K0r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K12l; move K12l before pvzI15; pose proof (proj2 pvzI15) as K12r; move K12r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K16l; move K16l before pvzI16; pose proof (proj2 pvzI16) as K16r; move K16r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K17l; move K17l before pvzI17; pose proof (proj2 pvzI17) as K17r; move K17r before pvzI17; clear pvzI17.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 38%nat => Z_to_bv 64 vz_38 | 40%nat => Z_to_bv 64 vz_40 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 38%nat => vz_38 | 40%nat => vz_40 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 69%nat. }
  assert (HR: regs_ok E PdkRT.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdkRT.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdkRT.kn0).
  { unfold know_ok, PdkRT.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV61l HV61r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV63l HV63r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K12l K12r K14; lia | clear - HV33l HV33r K12l K12r K14; lia | clear - HV33l HV33r K12l K12r K14; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PdkRT.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PdkRT.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PdkRT.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PdkRT.ps0) with 0x38c94 in Hms. change (SR.ps_regs PdkRT.ps0) with (map (fun i => (i, nth i PdkRT.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PdkRT.ps0) with PdkRT.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkRT.regs0 PdkRT.regs_out0 80 KS_dkRT_0 KS_dkRT_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PdkRT.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PdkRT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkRT.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PdkRT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkRT.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PdkRT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  - right.
    change (SR.ps_pc PdkRT.ps1) with 0x38bc4 in Hms. change (SR.ps_regs PdkRT.ps1) with (map (fun i => (i, nth i PdkRT.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PdkRT.ps1) with PdkRT.cells1 in Hcells. unfold PdkRT.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkRT.regs0 PdkRT.regs_out1 80 KS_dkRT_1 KS_dkRT_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PdkRT.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PdkRT.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkRT.regs_out1 E' R' 14 Hregs) by (clear; lia). cbn [nth PdkRT.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkRT.regs_out1 E' R' 19 Hregs) by (clear; lia). cbn [nth PdkRT.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
Qed.
(* [comment removed for export] *)

End PNSDRP.
