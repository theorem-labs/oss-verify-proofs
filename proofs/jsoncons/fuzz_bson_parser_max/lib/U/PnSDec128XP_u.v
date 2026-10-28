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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.seg Require LibSegBs_dkXA_u LibSegBs_dkXP_u LibSegBs_dkXL1a_u LibSegBs_dkXL1b_u LibSegBs_dkXD_u LibSegBs_dkXL2a_u LibSegBs_dkXL2b_u LibSegBs_dkXN0_u LibSegBs_dkXN1_u LibSegBs_dkXN2_u LibSegBs_dkXN3_u LibSegBs_dkXN4_u LibSegBs_dkXN5_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNSDXP.
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
Module PdkXA := LibSegBs_dkXA_u.
Definition KS_dkXA : list nat := Eval vm_compute in (BG.kept_list 80 PdkXA.regs0 PdkXA.regs_out0).
Lemma KS_dkXA_ok : BG.kept_ok 80 PdkXA.regs0 PdkXA.regs_out0 KS_dkXA = true. Proof. vm_compute. reflexivity. Qed.
Lemma dkXA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 42) -> getr R (reg 12) = Z_to_bv 64 (V 55%nat) -> getr R (reg 15) = Z_to_bv 64 ((V 50%nat) - 6176) ->
  140735332483312 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) ->
  4096 <= (V 33%nat) <= 140737488355286 -> L5.writable RSEGS M (V 33%nat) 42 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 42 <= ((V 2%nat) - 256)) -> L5.img_clear M 65536 754672 ->
  0 <= (V 50%nat) <= 16383 -> 0 <= (V 38%nat) <= 1 -> 1 <= (V 55%nat) <= 36 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38e44 M) (st fx' R' 0x38e48 M')
        /\ (forall x, In x KS_dkXA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 50%nat) + (V 55%nat)) - 6176)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 G2 G8 G12 G15 pvzI15 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 pvzI16 K13 K14 K15 pvzI17 pvzI18 pvzI19.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV50l; move HV50l before pvzI4; pose proof (proj2 pvzI4) as HV50r; move HV50r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV55l; move HV55l before pvzI5; pose proof (proj2 pvzI5) as HV55r; move HV55r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV60l; move HV60l before pvzI6; pose proof (proj2 pvzI6) as HV60r; move HV60r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV61l; move HV61l before pvzI7; pose proof (proj2 pvzI7) as HV61r; move HV61r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV62l; move HV62l before pvzI8; pose proof (proj2 pvzI8) as HV62r; move HV62r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV63l; move HV63l before pvzI9; pose proof (proj2 pvzI9) as HV63r; move HV63r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV64l; move HV64l before pvzI10; pose proof (proj2 pvzI10) as HV64r; move HV64r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV65l; move HV65l before pvzI11; pose proof (proj2 pvzI11) as HV65r; move HV65r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV66l; move HV66l before pvzI12; pose proof (proj2 pvzI12) as HV66r; move HV66r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV67l; move HV67l before pvzI13; pose proof (proj2 pvzI13) as HV67r; move HV67r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV68l; move HV68l before pvzI14; pose proof (proj2 pvzI14) as HV68r; move HV68r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K0l; move K0l before pvzI15; pose proof (proj2 pvzI15) as K0r; move K0r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K12l; move K12l before pvzI16; pose proof (proj2 pvzI16) as K12r; move K12r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K16l; move K16l before pvzI17; pose proof (proj2 pvzI17) as K16r; move K16r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K17l; move K17l before pvzI18; pose proof (proj2 pvzI18) as K17r; move K17r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K18l; move K18l before pvzI19; pose proof (proj2 pvzI19) as K18r; move K18r before pvzI19; clear pvzI19.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 38%nat => Z_to_bv 64 vz_38 | 50%nat => Z_to_bv 64 vz_50 | 55%nat => Z_to_bv 64 vz_55 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 38%nat => vz_38 | 50%nat => vz_50 | 55%nat => vz_55 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 69%nat. }
  assert (HR: regs_ok E PdkXA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdkXA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdkXA.kn0).
  { unfold know_ok, PdkXA.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV55l HV55r K18l K18r) | exact (conj K18l K18r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PdkXA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PdkXA.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PdkXA.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PdkXA.ps0) with 0x38e48 in Hms. change (SR.ps_regs PdkXA.ps0) with (map (fun i => (i, nth i PdkXA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PdkXA.ps0) with PdkXA.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkXA.regs0 PdkXA.regs_out0 80 KS_dkXA KS_dkXA_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg PdkXA.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PdkXA.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PdkXP := LibSegBs_dkXP_u.
Definition KS_dkXP : list nat := Eval vm_compute in (BG.kept_list 80 PdkXP.regs0 PdkXP.regs_out0).
Lemma KS_dkXP_ok : BG.kept_ok 80 PdkXP.regs0 PdkXP.regs_out0 KS_dkXP = true. Proof. vm_compute. reflexivity. Qed.
Lemma dkXP_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 42) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + (V 38%nat)) -> getr R (reg 11) = Z_to_bv 64 (V 59%nat) ->
  140735332483312 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) ->
  4096 <= (V 33%nat) <= 140737488355286 -> L5.writable RSEGS M (V 33%nat) 42 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 42 <= ((V 2%nat) - 256)) -> L5.img_clear M 65536 754672 ->
  0 <= (V 50%nat) <= 16383 -> 0 <= (V 38%nat) <= 1 -> 1 <= (V 55%nat) <= 36 -> 1 <= (V 59%nat) <= 35 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38e48 M) (st fx' R' 0x38e68 M')
        /\ (forall x, In x KS_dkXP -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 18446744073709551611
        /\ getr R' (reg 6) = Z_to_bv 64 2
        /\ getr R' (reg 7) = Z_to_bv 64 ((V 33%nat) + (V 38%nat))
        /\ getr R' (reg 14) = getr R (reg 13)
        /\ bv_unsigned (getr R' (reg 16)) = (Z.land (bv_unsigned (getr R (reg 13))) 3)
        /\ getr R' (reg 17) = Z_to_bv 64 1).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 G2 G8 G9 G11 pvzI16 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 pvzI17 K13 K14 K15 pvzI18 pvzI19 pvzI20 pvzI21.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV50l; move HV50l before pvzI4; pose proof (proj2 pvzI4) as HV50r; move HV50r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV55l; move HV55l before pvzI5; pose proof (proj2 pvzI5) as HV55r; move HV55r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV59l; move HV59l before pvzI6; pose proof (proj2 pvzI6) as HV59r; move HV59r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV60l; move HV60l before pvzI7; pose proof (proj2 pvzI7) as HV60r; move HV60r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV61l; move HV61l before pvzI8; pose proof (proj2 pvzI8) as HV61r; move HV61r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV62l; move HV62l before pvzI9; pose proof (proj2 pvzI9) as HV62r; move HV62r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV63l; move HV63l before pvzI10; pose proof (proj2 pvzI10) as HV63r; move HV63r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV64l; move HV64l before pvzI11; pose proof (proj2 pvzI11) as HV64r; move HV64r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV65l; move HV65l before pvzI12; pose proof (proj2 pvzI12) as HV65r; move HV65r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV66l; move HV66l before pvzI13; pose proof (proj2 pvzI13) as HV66r; move HV66r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV67l; move HV67l before pvzI14; pose proof (proj2 pvzI14) as HV67r; move HV67r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV68l; move HV68l before pvzI15; pose proof (proj2 pvzI15) as HV68r; move HV68r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K0l; move K0l before pvzI16; pose proof (proj2 pvzI16) as K0r; move K0r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K12l; move K12l before pvzI17; pose proof (proj2 pvzI17) as K12r; move K12r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K16l; move K16l before pvzI18; pose proof (proj2 pvzI18) as K16r; move K16r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K17l; move K17l before pvzI19; pose proof (proj2 pvzI19) as K17r; move K17r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K18l; move K18l before pvzI20; pose proof (proj2 pvzI20) as K18r; move K18r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K19l; move K19l before pvzI21; pose proof (proj2 pvzI21) as K19r; move K19r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_59 := V 59%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 38%nat => Z_to_bv 64 vz_38 | 50%nat => Z_to_bv 64 vz_50 | 55%nat => Z_to_bv 64 vz_55 | 59%nat => Z_to_bv 64 vz_59 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 38%nat => vz_38 | 50%nat => vz_50 | 55%nat => vz_55 | 59%nat => vz_59 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 69%nat. }
  assert (HR: regs_ok E PdkXP.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdkXP.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdkXP.kn0).
  { unfold know_ok, PdkXP.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV55l HV55r K18l K18r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV59l HV59r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PdkXP.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PdkXP.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PdkXP.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PdkXP.ps0) with 0x38e68 in Hms. change (SR.ps_regs PdkXP.ps0) with (map (fun i => (i, nth i PdkXP.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PdkXP.ps0) with PdkXP.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkXP.regs0 PdkXP.regs_out0 80 KS_dkXP KS_dkXP_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PdkXP.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PdkXP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkXP.regs_out0 E' R' 6 Hregs) by (clear; lia). cbn [nth PdkXP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkXP.regs_out0 E' R' 7 Hregs) by (clear; lia). cbn [nth PdkXP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkXP.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PdkXP.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PdkXP.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PdkXP.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
  rewrite (BG.out_reg PdkXP.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PdkXP.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PdkXL1a := LibSegBs_dkXL1a_u.
Definition KS_dkXL1a : list nat := Eval vm_compute in (BG.kept_list 80 PdkXL1a.regs0 PdkXL1a.regs_out0).
Lemma KS_dkXL1a_ok : BG.kept_ok 80 PdkXL1a.regs0 PdkXL1a.regs_out0 KS_dkXL1a = true. Proof. vm_compute. reflexivity. Qed.
Lemma dkXL1a_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 5) = Z_to_bv 64 (-5) -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 ((V 33%nat) + (V 57%nat)) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 42) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + (V 57%nat)) -> getr R (reg 11) = Z_to_bv 64 (V 59%nat) -> getr R (reg 13) = Z_to_bv 64 (((V 2%nat) - 216) + (V 58%nat)) -> getr R (reg 14) = Z_to_bv 64 (((V 2%nat) - 216) + (V 58%nat)) -> getr R (reg 16) = Z_to_bv 64 0 -> getr R (reg 17) = Z_to_bv 64 (V 70%nat) ->
  140735332483312 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) ->
  4096 <= (V 33%nat) <= 140737488355286 -> L5.writable RSEGS M (V 33%nat) 42 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 42 <= ((V 2%nat) - 256)) -> L5.img_clear M 65536 754672 ->
  0 <= (V 50%nat) <= 16383 -> 0 <= (V 38%nat) <= 1 -> 1 <= (V 55%nat) <= 36 -> 1 <= (V 59%nat) <= 35 ->
  1 <= (V 70%nat) <= 35 -> 0 <= (V 57%nat) <= 35 -> 0 <= (V 58%nat) <= 140 -> L5.defined M ((V 2%nat) - 216) 144 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 42) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 42) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38e68 M) (st fx' R' 0x38e90 M')
        /\ (forall x, In x KS_dkXL1a -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 7) = Z_to_bv 64 (((V 33%nat) + (V 57%nat)) + 1)
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 2%nat) + (V 58%nat)) - 212)
        /\ getr R' (reg 14) = Z_to_bv 64 (((V 2%nat) + (V 58%nat)) - 212)
        /\ getr R' (reg 15) = Z_to_bv 64 (((V 33%nat) + (V 57%nat)) + 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 G2 G5 G6 G7 G8 G9 G11 G13 G14 G16 G17 pvzI19 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 pvzI20 K13 K14 K15 pvzI21 pvzI22 pvzI23 pvzI24 pvzI25 pvzI26 pvzI27 K23.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV50l; move HV50l before pvzI4; pose proof (proj2 pvzI4) as HV50r; move HV50r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV55l; move HV55l before pvzI5; pose proof (proj2 pvzI5) as HV55r; move HV55r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV57l; move HV57l before pvzI6; pose proof (proj2 pvzI6) as HV57r; move HV57r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV58l; move HV58l before pvzI7; pose proof (proj2 pvzI7) as HV58r; move HV58r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV59l; move HV59l before pvzI8; pose proof (proj2 pvzI8) as HV59r; move HV59r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV60l; move HV60l before pvzI9; pose proof (proj2 pvzI9) as HV60r; move HV60r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV61l; move HV61l before pvzI10; pose proof (proj2 pvzI10) as HV61r; move HV61r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV62l; move HV62l before pvzI11; pose proof (proj2 pvzI11) as HV62r; move HV62r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV63l; move HV63l before pvzI12; pose proof (proj2 pvzI12) as HV63r; move HV63r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV64l; move HV64l before pvzI13; pose proof (proj2 pvzI13) as HV64r; move HV64r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV65l; move HV65l before pvzI14; pose proof (proj2 pvzI14) as HV65r; move HV65r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV66l; move HV66l before pvzI15; pose proof (proj2 pvzI15) as HV66r; move HV66r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV67l; move HV67l before pvzI16; pose proof (proj2 pvzI16) as HV67r; move HV67r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV68l; move HV68l before pvzI17; pose proof (proj2 pvzI17) as HV68r; move HV68r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV70l; move HV70l before pvzI18; pose proof (proj2 pvzI18) as HV70r; move HV70r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K0l; move K0l before pvzI19; pose proof (proj2 pvzI19) as K0r; move K0r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K12l; move K12l before pvzI20; pose proof (proj2 pvzI20) as K12r; move K12r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K16l; move K16l before pvzI21; pose proof (proj2 pvzI21) as K16r; move K16r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K17l; move K17l before pvzI22; pose proof (proj2 pvzI22) as K17r; move K17r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K18l; move K18l before pvzI23; pose proof (proj2 pvzI23) as K18r; move K18r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K19l; move K19l before pvzI24; pose proof (proj2 pvzI24) as K19r; move K19r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K20l; move K20l before pvzI25; pose proof (proj2 pvzI25) as K20r; move K20r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K21l; move K21l before pvzI26; pose proof (proj2 pvzI26) as K21r; move K21r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as K22l; move K22l before pvzI27; pose proof (proj2 pvzI27) as K22r; move K22r before pvzI27; clear pvzI27.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *. set (vz_59 := V 59%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_70 := V 70%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 38%nat => Z_to_bv 64 vz_38 | 50%nat => Z_to_bv 64 vz_50 | 55%nat => Z_to_bv 64 vz_55 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | 59%nat => Z_to_bv 64 vz_59 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 70%nat => Z_to_bv 64 vz_70 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 38%nat => vz_38 | 50%nat => vz_50 | 55%nat => vz_55 | 57%nat => vz_57 | 58%nat => vz_58 | 59%nat => vz_59 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 70%nat => vz_70 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 71%nat. }
  assert (HR: regs_ok E PdkXL1a.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdkXL1a.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdkXL1a.kn0).
  { unfold know_ok, PdkXL1a.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV55l HV55r K18l K18r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV59l HV59r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV70l HV70r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV57l HV57r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV58l HV58r K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K23]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PdkXL1a.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PdkXL1a.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_33 + 0) <= bv_unsigned a < (vz_33 + 0) + 42) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PdkXL1a.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K12l K12r K14 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PdkXL1a.ps0) with 0x38e90 in Hms. change (SR.ps_regs PdkXL1a.ps0) with (map (fun i => (i, nth i PdkXL1a.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PdkXL1a.ps0) with PdkXL1a.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkXL1a.regs0 PdkXL1a.regs_out0 80 KS_dkXL1a KS_dkXL1a_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PdkXL1a.regs_out0 E' R' 7 Hregs) by (clear; lia). cbn [nth PdkXL1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkXL1a.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PdkXL1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkXL1a.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PdkXL1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PdkXL1a.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PdkXL1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PdkXL1b := LibSegBs_dkXL1b_u.
Definition KS_dkXL1b_0 : list nat := Eval vm_compute in (BG.kept_list 80 PdkXL1b.regs0 PdkXL1b.regs_out0).
Lemma KS_dkXL1b_0_ok : BG.kept_ok 80 PdkXL1b.regs0 PdkXL1b.regs_out0 KS_dkXL1b_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_dkXL1b_1 : list nat := Eval vm_compute in (BG.kept_list 80 PdkXL1b.regs0 PdkXL1b.regs_out1).
Lemma KS_dkXL1b_1_ok : BG.kept_ok 80 PdkXL1b.regs0 PdkXL1b.regs_out1 KS_dkXL1b_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dkXL1b_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 42) -> getr R (reg 10) = Z_to_bv 64 (((V 2%nat) - 216) + (V 58%nat)) -> getr R (reg 11) = Z_to_bv 64 (V 59%nat) -> getr R (reg 15) = Z_to_bv 64 ((V 33%nat) + (V 57%nat)) -> getr R (reg 17) = Z_to_bv 64 (V 70%nat) ->
  140735332483312 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) ->
  4096 <= (V 33%nat) <= 140737488355286 -> L5.writable RSEGS M (V 33%nat) 42 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 42 <= ((V 2%nat) - 256)) -> L5.img_clear M 65536 754672 ->
  0 <= (V 50%nat) <= 16383 -> 0 <= (V 38%nat) <= 1 -> 1 <= (V 55%nat) <= 36 -> 1 <= (V 59%nat) <= 35 ->
  1 <= (V 70%nat) <= 35 -> 1 <= (V 57%nat) <= 36 -> 0 <= (V 58%nat) <= 144 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x38e90 M) (st fx' R' 0x38e68 M')
        /\ (forall x, In x KS_dkXL1b_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 33%nat) + (V 57%nat))
        /\ getr R' (reg 13) = Z_to_bv 64 (((V 2%nat) + (V 58%nat)) - 216)
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 70%nat) + 1)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | 55%nat => Z_to_bv 64 (V 55%nat) | 57%nat => Z_to_bv 64 (V 57%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 59%nat => Z_to_bv 64 (V 59%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | 63%nat => Z_to_bv 64 (V 63%nat) | 64%nat => Z_to_bv 64 (V 64%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 66%nat => Z_to_bv 64 (V 66%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | 70%nat => Z_to_bv 64 (V 70%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EVar 70) (EVar 59))) <= 1)
      \/ (msteps RSEGS (st fx R 0x38e90 M) (st fx' R' 0x38fc4 M')
        /\ (forall x, In x KS_dkXL1b_1 -> getr R' (reg x) = getr R (reg x))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | 55%nat => Z_to_bv 64 (V 55%nat) | 57%nat => Z_to_bv 64 (V 57%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 59%nat => Z_to_bv 64 (V 59%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | 63%nat => Z_to_bv 64 (V 63%nat) | 64%nat => Z_to_bv 64 (V 64%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 66%nat => Z_to_bv 64 (V 66%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | 70%nat => Z_to_bv 64 (V 70%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EVar 70) (EVar 59))) <= 0)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 G2 G8 G10 G11 G15 G17 pvzI19 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 pvzI20 K13 K14 K15 pvzI21 pvzI22 pvzI23 pvzI24 pvzI25 pvzI26 pvzI27.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV50l; move HV50l before pvzI4; pose proof (proj2 pvzI4) as HV50r; move HV50r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV55l; move HV55l before pvzI5; pose proof (proj2 pvzI5) as HV55r; move HV55r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV57l; move HV57l before pvzI6; pose proof (proj2 pvzI6) as HV57r; move HV57r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV58l; move HV58l before pvzI7; pose proof (proj2 pvzI7) as HV58r; move HV58r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV59l; move HV59l before pvzI8; pose proof (proj2 pvzI8) as HV59r; move HV59r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV60l; move HV60l before pvzI9; pose proof (proj2 pvzI9) as HV60r; move HV60r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV61l; move HV61l before pvzI10; pose proof (proj2 pvzI10) as HV61r; move HV61r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV62l; move HV62l before pvzI11; pose proof (proj2 pvzI11) as HV62r; move HV62r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV63l; move HV63l before pvzI12; pose proof (proj2 pvzI12) as HV63r; move HV63r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV64l; move HV64l before pvzI13; pose proof (proj2 pvzI13) as HV64r; move HV64r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV65l; move HV65l before pvzI14; pose proof (proj2 pvzI14) as HV65r; move HV65r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV66l; move HV66l before pvzI15; pose proof (proj2 pvzI15) as HV66r; move HV66r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV67l; move HV67l before pvzI16; pose proof (proj2 pvzI16) as HV67r; move HV67r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV68l; move HV68l before pvzI17; pose proof (proj2 pvzI17) as HV68r; move HV68r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV70l; move HV70l before pvzI18; pose proof (proj2 pvzI18) as HV70r; move HV70r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K0l; move K0l before pvzI19; pose proof (proj2 pvzI19) as K0r; move K0r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K12l; move K12l before pvzI20; pose proof (proj2 pvzI20) as K12r; move K12r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K16l; move K16l before pvzI21; pose proof (proj2 pvzI21) as K16r; move K16r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K17l; move K17l before pvzI22; pose proof (proj2 pvzI22) as K17r; move K17r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K18l; move K18l before pvzI23; pose proof (proj2 pvzI23) as K18r; move K18r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K19l; move K19l before pvzI24; pose proof (proj2 pvzI24) as K19r; move K19r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K20l; move K20l before pvzI25; pose proof (proj2 pvzI25) as K20r; move K20r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K21l; move K21l before pvzI26; pose proof (proj2 pvzI26) as K21r; move K21r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as K22l; move K22l before pvzI27; pose proof (proj2 pvzI27) as K22r; move K22r before pvzI27; clear pvzI27.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *. set (vz_59 := V 59%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_70 := V 70%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 38%nat => Z_to_bv 64 vz_38 | 50%nat => Z_to_bv 64 vz_50 | 55%nat => Z_to_bv 64 vz_55 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | 59%nat => Z_to_bv 64 vz_59 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 70%nat => Z_to_bv 64 vz_70 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 38%nat => vz_38 | 50%nat => vz_50 | 55%nat => vz_55 | 57%nat => vz_57 | 58%nat => vz_58 | 59%nat => vz_59 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 70%nat => vz_70 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 71%nat. }
  assert (HR: regs_ok E PdkXL1b.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdkXL1b.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdkXL1b.kn0).
  { unfold know_ok, PdkXL1b.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV55l HV55r K18l K18r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV59l HV59r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV70l HV70r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV57l HV57r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV58l HV58r K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PdkXL1b.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PdkXL1b.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PdkXL1b.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PdkXL1b.ps0) with 0x38e68 in Hms. change (SR.ps_regs PdkXL1b.ps0) with (map (fun i => (i, nth i PdkXL1b.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PdkXL1b.ps0) with PdkXL1b.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkXL1b.regs0 PdkXL1b.regs_out0 80 KS_dkXL1b_0 KS_dkXL1b_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PdkXL1b.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PdkXL1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkXL1b.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PdkXL1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkXL1b.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PdkXL1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. 
  - right.
    change (SR.ps_pc PdkXL1b.ps1) with 0x38fc4 in Hms. change (SR.ps_regs PdkXL1b.ps1) with (map (fun i => (i, nth i PdkXL1b.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PdkXL1b.ps1) with PdkXL1b.cells1 in Hcells. unfold PdkXL1b.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkXL1b.regs0 PdkXL1b.regs_out1 80 KS_dkXL1b_1 KS_dkXL1b_1_ok HR Hag Hregs j Hj). }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PdkXD := LibSegBs_dkXD_u.
Definition KS_dkXD_0 : list nat := Eval vm_compute in (BG.kept_list 80 PdkXD.regs0 PdkXD.regs_out0).
Lemma KS_dkXD_0_ok : BG.kept_ok 80 PdkXD.regs0 PdkXD.regs_out0 KS_dkXD_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_dkXD_1 : list nat := Eval vm_compute in (BG.kept_list 80 PdkXD.regs0 PdkXD.regs_out1).
Lemma KS_dkXD_1_ok : BG.kept_ok 80 PdkXD.regs0 PdkXD.regs_out1 KS_dkXD_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dkXD_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 42) -> getr R (reg 10) = Z_to_bv 64 (((V 2%nat) - 216) + (V 58%nat)) -> getr R (reg 11) = Z_to_bv 64 (V 59%nat) -> getr R (reg 12) = Z_to_bv 64 (V 55%nat) -> getr R (reg 14) = Z_to_bv 64 (((V 2%nat) - 216) + (V 58%nat)) -> getr R (reg 15) = Z_to_bv 64 ((V 33%nat) + (V 57%nat)) ->
  140735332483312 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) ->
  4096 <= (V 33%nat) <= 140737488355286 -> L5.writable RSEGS M (V 33%nat) 42 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 42 <= ((V 2%nat) - 256)) -> L5.img_clear M 65536 754672 ->
  0 <= (V 50%nat) <= 16383 -> 0 <= (V 38%nat) <= 1 -> 1 <= (V 55%nat) <= 36 -> 1 <= (V 59%nat) <= 35 ->
  1 <= (V 57%nat) <= 36 -> 0 <= (V 58%nat) <= 144 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 42) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 42) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x38fc4 M) (st fx' R' 0x38f6c M')
        /\ (forall x, In x KS_dkXD_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 ((V 59%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 (((V 33%nat) + (V 57%nat)) + 1)
        /\ getr R' (reg 15) = Z_to_bv 64 (V 59%nat)
        /\ getr R' (reg 16) = Z_to_bv 64 48
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 59%nat) + 1)
        /\ getr R' (reg 19) = Z_to_bv 64 (((V 33%nat) + (V 57%nat)) + 1)
        /\ (((V 55%nat) - (V 59%nat)) mod 2 ^ 64) < 1
        /\ L5.u8_at RSEGS M' ((V 33%nat) + (V 57%nat)) 46)
      \/ (msteps RSEGS (st fx R 0x38fc4 M) (st fx' R' 0x39048 M')
        /\ (forall x, In x KS_dkXD_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 ((V 59%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 (((V 33%nat) + (V 57%nat)) + 1)
        /\ bv_unsigned (getr R' (reg 14)) = (Z.land (V 58%nat) 3)
        /\ bv_unsigned (getr R' (reg 15)) = (((((4294967296 * (V 55%nat)) mod 2 ^ 64) + ((18446744069414584320 * (V 59%nat)) mod 2 ^ 64)) mod 2 ^ 64) / 4294967296)
        /\ getr R' (reg 16) = Z_to_bv 64 18446744073709551611
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 59%nat) + 1)
        /\ 1 <= (((V 55%nat) - (V 59%nat)) mod 2 ^ 64)
        /\ L5.u8_at RSEGS M' ((V 33%nat) + (V 57%nat)) 46)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 G2 G8 G10 G11 G12 G14 G15 pvzI18 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 pvzI19 K13 K14 K15 pvzI20 pvzI21 pvzI22 pvzI23 pvzI24 pvzI25.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV50l; move HV50l before pvzI4; pose proof (proj2 pvzI4) as HV50r; move HV50r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV55l; move HV55l before pvzI5; pose proof (proj2 pvzI5) as HV55r; move HV55r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV57l; move HV57l before pvzI6; pose proof (proj2 pvzI6) as HV57r; move HV57r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV58l; move HV58l before pvzI7; pose proof (proj2 pvzI7) as HV58r; move HV58r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV59l; move HV59l before pvzI8; pose proof (proj2 pvzI8) as HV59r; move HV59r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV60l; move HV60l before pvzI9; pose proof (proj2 pvzI9) as HV60r; move HV60r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV61l; move HV61l before pvzI10; pose proof (proj2 pvzI10) as HV61r; move HV61r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV62l; move HV62l before pvzI11; pose proof (proj2 pvzI11) as HV62r; move HV62r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV63l; move HV63l before pvzI12; pose proof (proj2 pvzI12) as HV63r; move HV63r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV64l; move HV64l before pvzI13; pose proof (proj2 pvzI13) as HV64r; move HV64r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV65l; move HV65l before pvzI14; pose proof (proj2 pvzI14) as HV65r; move HV65r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV66l; move HV66l before pvzI15; pose proof (proj2 pvzI15) as HV66r; move HV66r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV67l; move HV67l before pvzI16; pose proof (proj2 pvzI16) as HV67r; move HV67r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV68l; move HV68l before pvzI17; pose proof (proj2 pvzI17) as HV68r; move HV68r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K0l; move K0l before pvzI18; pose proof (proj2 pvzI18) as K0r; move K0r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K12l; move K12l before pvzI19; pose proof (proj2 pvzI19) as K12r; move K12r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K16l; move K16l before pvzI20; pose proof (proj2 pvzI20) as K16r; move K16r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K17l; move K17l before pvzI21; pose proof (proj2 pvzI21) as K17r; move K17r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K18l; move K18l before pvzI22; pose proof (proj2 pvzI22) as K18r; move K18r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K19l; move K19l before pvzI23; pose proof (proj2 pvzI23) as K19r; move K19r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K20l; move K20l before pvzI24; pose proof (proj2 pvzI24) as K20r; move K20r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K21l; move K21l before pvzI25; pose proof (proj2 pvzI25) as K21r; move K21r before pvzI25; clear pvzI25.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *. set (vz_59 := V 59%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 38%nat => Z_to_bv 64 vz_38 | 50%nat => Z_to_bv 64 vz_50 | 55%nat => Z_to_bv 64 vz_55 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | 59%nat => Z_to_bv 64 vz_59 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 38%nat => vz_38 | 50%nat => vz_50 | 55%nat => vz_55 | 57%nat => vz_57 | 58%nat => vz_58 | 59%nat => vz_59 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 69%nat. }
  assert (HR: regs_ok E PdkXD.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdkXD.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdkXD.kn0).
  { unfold know_ok, PdkXD.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV55l HV55r K18l K18r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV59l HV59r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV57l HV57r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV58l HV58r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PdkXD.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PdkXD.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_33 + 0) <= bv_unsigned a < (vz_33 + 0) + 42) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PdkXD.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K12l K12r K14 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PdkXD.ps0) with 0x38f6c in Hms. change (SR.ps_regs PdkXD.ps0) with (map (fun i => (i, nth i PdkXD.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PdkXD.ps0) with PdkXD.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkXD.regs0 PdkXD.regs_out0 80 KS_dkXD_0 KS_dkXD_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PdkXD.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PdkXD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkXD.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PdkXD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkXD.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PdkXD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkXD.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PdkXD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkXD.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PdkXD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkXD.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PdkXD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkXD.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PdkXD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K12l K12r K14 HV57l HV57r K20l K20r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. 
  - right.
    change (SR.ps_pc PdkXD.ps1) with 0x39048 in Hms. change (SR.ps_regs PdkXD.ps1) with (map (fun i => (i, nth i PdkXD.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PdkXD.ps1) with PdkXD.cells1 in Hcells. unfold PdkXD.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkXD.regs0 PdkXD.regs_out1 80 KS_dkXD_1 KS_dkXD_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PdkXD.regs_out1 E' R' 5 Hregs) by (clear; lia). cbn [nth PdkXD.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkXD.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PdkXD.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkXD.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PdkXD.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkXD.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PdkXD.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkXD.regs_out1 E' R' 14 Hregs) by (clear; lia). cbn [nth PdkXD.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PdkXD.regs_out1 E' R' 15 Hregs) by (clear; lia). cbn [nth PdkXD.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PdkXD.regs_out1 E' R' 16 Hregs) by (clear; lia). cbn [nth PdkXD.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkXD.regs_out1 E' R' 17 Hregs) by (clear; lia). cbn [nth PdkXD.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K12l K12r K14 HV57l HV57r K20l K20r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PdkXL2a := LibSegBs_dkXL2a_u.
Definition KS_dkXL2a : list nat := Eval vm_compute in (BG.kept_list 80 PdkXL2a.regs0 PdkXL2a.regs_out0).
Lemma KS_dkXL2a_ok : BG.kept_ok 80 PdkXL2a.regs0 PdkXL2a.regs_out0 KS_dkXL2a = true. Proof. vm_compute. reflexivity. Qed.
Lemma dkXL2a_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 42) -> getr R (reg 10) = Z_to_bv 64 (((V 2%nat) - 216) + (V 58%nat)) -> getr R (reg 12) = Z_to_bv 64 ((V 72%nat) + 1) -> getr R (reg 13) = Z_to_bv 64 (((V 33%nat) + (V 57%nat)) + (V 72%nat)) -> getr R (reg 14) = Z_to_bv 64 0 -> getr R (reg 15) = Z_to_bv 64 (V 71%nat) -> getr R (reg 16) = Z_to_bv 64 (-5) ->
  140735332483312 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) ->
  4096 <= (V 33%nat) <= 140737488355286 -> L5.writable RSEGS M (V 33%nat) 42 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 42 <= ((V 2%nat) - 256)) -> L5.img_clear M 65536 754672 ->
  0 <= (V 50%nat) <= 16383 -> 0 <= (V 38%nat) <= 1 -> 1 <= (V 55%nat) <= 36 -> 1 <= (V 71%nat) <= 36 ->
  0 <= (V 72%nat) <= 35 -> 2 <= (V 57%nat) <= 41 -> 0 <= (V 58%nat) <= 140 -> 2 <= ((V 57%nat) + (V 72%nat)) <= 41 ->
  L5.defined M ((V 2%nat) - 216) 144 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 42) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 42) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x39048 M) (st fx' R' 0x39060 M')
        /\ (forall x, In x KS_dkXL2a -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 19) = Z_to_bv 64 (((V 33%nat) + ((V 57%nat) + (V 72%nat))) + 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 G2 G8 G10 G12 G13 G14 G15 G16 pvzI19 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 pvzI20 K13 K14 K15 pvzI21 pvzI22 pvzI23 pvzI24 pvzI25 pvzI26 pvzI27 pvzI28 K24.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV50l; move HV50l before pvzI4; pose proof (proj2 pvzI4) as HV50r; move HV50r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV55l; move HV55l before pvzI5; pose proof (proj2 pvzI5) as HV55r; move HV55r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV57l; move HV57l before pvzI6; pose proof (proj2 pvzI6) as HV57r; move HV57r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV58l; move HV58l before pvzI7; pose proof (proj2 pvzI7) as HV58r; move HV58r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV60l; move HV60l before pvzI8; pose proof (proj2 pvzI8) as HV60r; move HV60r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV61l; move HV61l before pvzI9; pose proof (proj2 pvzI9) as HV61r; move HV61r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV62l; move HV62l before pvzI10; pose proof (proj2 pvzI10) as HV62r; move HV62r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV63l; move HV63l before pvzI11; pose proof (proj2 pvzI11) as HV63r; move HV63r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV64l; move HV64l before pvzI12; pose proof (proj2 pvzI12) as HV64r; move HV64r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV65l; move HV65l before pvzI13; pose proof (proj2 pvzI13) as HV65r; move HV65r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV66l; move HV66l before pvzI14; pose proof (proj2 pvzI14) as HV66r; move HV66r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV67l; move HV67l before pvzI15; pose proof (proj2 pvzI15) as HV67r; move HV67r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV68l; move HV68l before pvzI16; pose proof (proj2 pvzI16) as HV68r; move HV68r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV71l; move HV71l before pvzI17; pose proof (proj2 pvzI17) as HV71r; move HV71r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV72l; move HV72l before pvzI18; pose proof (proj2 pvzI18) as HV72r; move HV72r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K0l; move K0l before pvzI19; pose proof (proj2 pvzI19) as K0r; move K0r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K12l; move K12l before pvzI20; pose proof (proj2 pvzI20) as K12r; move K12r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K16l; move K16l before pvzI21; pose proof (proj2 pvzI21) as K16r; move K16r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K17l; move K17l before pvzI22; pose proof (proj2 pvzI22) as K17r; move K17r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K18l; move K18l before pvzI23; pose proof (proj2 pvzI23) as K18r; move K18r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K19l; move K19l before pvzI24; pose proof (proj2 pvzI24) as K19r; move K19r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K20l; move K20l before pvzI25; pose proof (proj2 pvzI25) as K20r; move K20r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K21l; move K21l before pvzI26; pose proof (proj2 pvzI26) as K21r; move K21r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as K22l; move K22l before pvzI27; pose proof (proj2 pvzI27) as K22r; move K22r before pvzI27; clear pvzI27. pose proof (proj1 pvzI28) as K23l; move K23l before pvzI28; pose proof (proj2 pvzI28) as K23r; move K23r before pvzI28; clear pvzI28.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 38%nat => Z_to_bv 64 vz_38 | 50%nat => Z_to_bv 64 vz_50 | 55%nat => Z_to_bv 64 vz_55 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 38%nat => vz_38 | 50%nat => vz_50 | 55%nat => vz_55 | 57%nat => vz_57 | 58%nat => vz_58 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 71%nat => vz_71 | 72%nat => vz_72 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 73%nat. }
  assert (HR: regs_ok E PdkXL2a.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdkXL2a.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdkXL2a.kn0).
  { unfold know_ok, PdkXL2a.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV55l HV55r K18l K18r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV71l HV71r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV72l HV72r K20l K20r K23l K23r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV57l HV57r K21l K21r K23l K23r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV58l HV58r K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV57l HV57r K21l K21r K23l K23r HV72l HV72r K20l K20r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | clear - HV2l HV2r K0l K0r K14; lia | exactA K24]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PdkXL2a.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PdkXL2a.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_33 + 0) <= bv_unsigned a < (vz_33 + 0) + 42) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PdkXL2a.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K12l K12r K14 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PdkXL2a.ps0) with 0x39060 in Hms. change (SR.ps_regs PdkXL2a.ps0) with (map (fun i => (i, nth i PdkXL2a.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PdkXL2a.ps0) with PdkXL2a.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkXL2a.regs0 PdkXL2a.regs_out0 80 KS_dkXL2a KS_dkXL2a_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg PdkXL2a.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PdkXL2a.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PdkXL2b := LibSegBs_dkXL2b_u.
Definition KS_dkXL2b_0 : list nat := Eval vm_compute in (BG.kept_list 80 PdkXL2b.regs0 PdkXL2b.regs_out0).
Lemma KS_dkXL2b_0_ok : BG.kept_ok 80 PdkXL2b.regs0 PdkXL2b.regs_out0 KS_dkXL2b_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_dkXL2b_1 : list nat := Eval vm_compute in (BG.kept_list 80 PdkXL2b.regs0 PdkXL2b.regs_out1).
Lemma KS_dkXL2b_1_ok : BG.kept_ok 80 PdkXL2b.regs0 PdkXL2b.regs_out1 KS_dkXL2b_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_dkXL2b_2 : list nat := Eval vm_compute in (BG.kept_list 80 PdkXL2b.regs0 PdkXL2b.regs_out2).
Lemma KS_dkXL2b_2_ok : BG.kept_ok 80 PdkXL2b.regs0 PdkXL2b.regs_out2 KS_dkXL2b_2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dkXL2b_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 42) -> getr R (reg 10) = Z_to_bv 64 (((V 2%nat) - 216) + (V 58%nat)) -> getr R (reg 12) = Z_to_bv 64 ((V 72%nat) + 1) -> getr R (reg 15) = Z_to_bv 64 (V 71%nat) -> getr R (reg 19) = Z_to_bv 64 ((((V 33%nat) + (V 57%nat)) + (V 72%nat)) + 1) ->
  140735332483312 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) ->
  4096 <= (V 33%nat) <= 140737488355286 -> L5.writable RSEGS M (V 33%nat) 42 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 42 <= ((V 2%nat) - 256)) -> L5.img_clear M 65536 754672 ->
  0 <= (V 50%nat) <= 16383 -> 0 <= (V 38%nat) <= 1 -> 1 <= (V 55%nat) <= 36 -> 1 <= (V 71%nat) <= 36 ->
  0 <= (V 72%nat) <= 35 -> 2 <= (V 57%nat) <= 41 -> 0 <= (V 58%nat) <= 140 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x39060 M) (st fx' R' 0x39048 M')
        /\ (forall x, In x KS_dkXL2b_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 2%nat) + (V 58%nat)) - 212)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 72%nat) + 2)
        /\ getr R' (reg 13) = Z_to_bv 64 (((V 33%nat) + ((V 57%nat) + (V 72%nat))) + 1)
        /\ (((((((V 33%nat) + (V 57%nat)) mod 2 ^ 64) + (V 72%nat)) mod 2 ^ 64) + 1) mod 2 ^ 64) < (((V 33%nat) + 42) mod 2 ^ 64)
        /\ (((V 72%nat) + 1) mod 2 ^ 64) < (V 71%nat))
      \/ (msteps RSEGS (st fx R 0x39060 M) (st fx' R' 0x38f6c M')
        /\ (forall x, In x KS_dkXL2b_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 2%nat) + (V 58%nat)) - 212)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 72%nat) + 2)
        /\ getr R' (reg 13) = Z_to_bv 64 (((V 33%nat) + ((V 57%nat) + (V 72%nat))) + 1)
        /\ (((V 33%nat) + 42) mod 2 ^ 64) <= (((((((V 33%nat) + (V 57%nat)) mod 2 ^ 64) + (V 72%nat)) mod 2 ^ 64) + 1) mod 2 ^ 64)
        /\ (((V 72%nat) + 1) mod 2 ^ 64) < (V 71%nat))
      \/ (msteps RSEGS (st fx R 0x39060 M) (st fx' R' 0x38f6c M')
        /\ (forall x, In x KS_dkXL2b_2 -> getr R' (reg x) = getr R (reg x))
        /\ (V 71%nat) <= (((V 72%nat) + 1) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 G2 G8 G10 G12 G15 G19 pvzI19 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 pvzI20 K13 K14 K15 pvzI21 pvzI22 pvzI23 pvzI24 pvzI25 pvzI26 pvzI27.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV50l; move HV50l before pvzI4; pose proof (proj2 pvzI4) as HV50r; move HV50r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV55l; move HV55l before pvzI5; pose proof (proj2 pvzI5) as HV55r; move HV55r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV57l; move HV57l before pvzI6; pose proof (proj2 pvzI6) as HV57r; move HV57r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV58l; move HV58l before pvzI7; pose proof (proj2 pvzI7) as HV58r; move HV58r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV60l; move HV60l before pvzI8; pose proof (proj2 pvzI8) as HV60r; move HV60r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV61l; move HV61l before pvzI9; pose proof (proj2 pvzI9) as HV61r; move HV61r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV62l; move HV62l before pvzI10; pose proof (proj2 pvzI10) as HV62r; move HV62r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV63l; move HV63l before pvzI11; pose proof (proj2 pvzI11) as HV63r; move HV63r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV64l; move HV64l before pvzI12; pose proof (proj2 pvzI12) as HV64r; move HV64r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV65l; move HV65l before pvzI13; pose proof (proj2 pvzI13) as HV65r; move HV65r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV66l; move HV66l before pvzI14; pose proof (proj2 pvzI14) as HV66r; move HV66r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV67l; move HV67l before pvzI15; pose proof (proj2 pvzI15) as HV67r; move HV67r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV68l; move HV68l before pvzI16; pose proof (proj2 pvzI16) as HV68r; move HV68r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV71l; move HV71l before pvzI17; pose proof (proj2 pvzI17) as HV71r; move HV71r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV72l; move HV72l before pvzI18; pose proof (proj2 pvzI18) as HV72r; move HV72r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K0l; move K0l before pvzI19; pose proof (proj2 pvzI19) as K0r; move K0r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K12l; move K12l before pvzI20; pose proof (proj2 pvzI20) as K12r; move K12r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K16l; move K16l before pvzI21; pose proof (proj2 pvzI21) as K16r; move K16r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K17l; move K17l before pvzI22; pose proof (proj2 pvzI22) as K17r; move K17r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K18l; move K18l before pvzI23; pose proof (proj2 pvzI23) as K18r; move K18r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K19l; move K19l before pvzI24; pose proof (proj2 pvzI24) as K19r; move K19r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K20l; move K20l before pvzI25; pose proof (proj2 pvzI25) as K20r; move K20r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K21l; move K21l before pvzI26; pose proof (proj2 pvzI26) as K21r; move K21r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as K22l; move K22l before pvzI27; pose proof (proj2 pvzI27) as K22r; move K22r before pvzI27; clear pvzI27.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 38%nat => Z_to_bv 64 vz_38 | 50%nat => Z_to_bv 64 vz_50 | 55%nat => Z_to_bv 64 vz_55 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 38%nat => vz_38 | 50%nat => vz_50 | 55%nat => vz_55 | 57%nat => vz_57 | 58%nat => vz_58 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 71%nat => vz_71 | 72%nat => vz_72 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 73%nat. }
  assert (HR: regs_ok E PdkXL2b.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdkXL2b.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdkXL2b.kn0).
  { unfold know_ok, PdkXL2b.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV55l HV55r K18l K18r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV71l HV71r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV72l HV72r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV57l HV57r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV58l HV58r K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PdkXL2b.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PdkXL2b.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PdkXL2b.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PdkXL2b.ps0) with 0x39048 in Hms. change (SR.ps_regs PdkXL2b.ps0) with (map (fun i => (i, nth i PdkXL2b.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PdkXL2b.ps0) with PdkXL2b.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkXL2b.regs0 PdkXL2b.regs_out0 80 KS_dkXL2b_0 KS_dkXL2b_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PdkXL2b.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PdkXL2b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkXL2b.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PdkXL2b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkXL2b.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PdkXL2b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. left.
    change (SR.ps_pc PdkXL2b.ps1) with 0x38f6c in Hms. change (SR.ps_regs PdkXL2b.ps1) with (map (fun i => (i, nth i PdkXL2b.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PdkXL2b.ps1) with PdkXL2b.cells1 in Hcells. unfold PdkXL2b.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkXL2b.regs0 PdkXL2b.regs_out1 80 KS_dkXL2b_1 KS_dkXL2b_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PdkXL2b.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PdkXL2b.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkXL2b.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PdkXL2b.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkXL2b.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PdkXL2b.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. 
    change (SR.ps_pc PdkXL2b.ps2) with 0x38f6c in Hms. change (SR.ps_regs PdkXL2b.ps2) with (map (fun i => (i, nth i PdkXL2b.regs_out2 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PdkXL2b.ps2) with PdkXL2b.cells2 in Hcells. unfold PdkXL2b.cells2 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkXL2b.regs0 PdkXL2b.regs_out2 80 KS_dkXL2b_2 KS_dkXL2b_2_ok HR Hag Hregs j Hj). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PdkXN0 := LibSegBs_dkXN0_u.
Definition KS_dkXN0 : list nat := Eval vm_compute in (BG.kept_list 80 PdkXN0.regs0 PdkXN0.regs_out0).
Lemma KS_dkXN0_ok : BG.kept_ok 80 PdkXN0.regs0 PdkXN0.regs_out0 KS_dkXN0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dkXN0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 42) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + (V 38%nat)) -> getr R (reg 11) = Z_to_bv 64 0 -> getr R (reg 12) = Z_to_bv 64 (V 55%nat) ->
  140735332483312 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) ->
  4096 <= (V 33%nat) <= 140737488355286 -> L5.writable RSEGS M (V 33%nat) 42 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 42 <= ((V 2%nat) - 256)) -> L5.img_clear M 65536 754672 ->
  0 <= (V 38%nat) <= 1 -> 1 <= (V 55%nat) <= 36 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 42) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 42) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38e48 M) (st fx' R' 0x39048 M')
        /\ (forall x, In x KS_dkXN0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 1
        /\ getr R' (reg 10) = getr R (reg 13)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 (((V 33%nat) + (V 38%nat)) + 2)
        /\ bv_unsigned (getr R' (reg 14)) = (Z.land (bv_unsigned (getr R (reg 13))) 3)
        /\ getr R' (reg 15) = Z_to_bv 64 (V 55%nat)
        /\ getr R' (reg 16) = Z_to_bv 64 18446744073709551611
        /\ getr R' (reg 17) = Z_to_bv 64 1
        /\ L5.u8_at RSEGS M' (((V 33%nat) + (V 38%nat)) + 1) 46
        /\ L5.u8_at RSEGS M' ((V 33%nat) + (V 38%nat)) 48).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 G2 G8 G9 G11 G12 pvzI14 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 pvzI15 K13 K14 K15 pvzI16 pvzI17.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV55l; move HV55l before pvzI4; pose proof (proj2 pvzI4) as HV55r; move HV55r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV60l; move HV60l before pvzI5; pose proof (proj2 pvzI5) as HV60r; move HV60r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV61l; move HV61l before pvzI6; pose proof (proj2 pvzI6) as HV61r; move HV61r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV62l; move HV62l before pvzI7; pose proof (proj2 pvzI7) as HV62r; move HV62r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV63l; move HV63l before pvzI8; pose proof (proj2 pvzI8) as HV63r; move HV63r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV64l; move HV64l before pvzI9; pose proof (proj2 pvzI9) as HV64r; move HV64r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV65l; move HV65l before pvzI10; pose proof (proj2 pvzI10) as HV65r; move HV65r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV66l; move HV66l before pvzI11; pose proof (proj2 pvzI11) as HV66r; move HV66r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV67l; move HV67l before pvzI12; pose proof (proj2 pvzI12) as HV67r; move HV67r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV68l; move HV68l before pvzI13; pose proof (proj2 pvzI13) as HV68r; move HV68r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K0l; move K0l before pvzI14; pose proof (proj2 pvzI14) as K0r; move K0r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K12l; move K12l before pvzI15; pose proof (proj2 pvzI15) as K12r; move K12r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K16l; move K16l before pvzI16; pose proof (proj2 pvzI16) as K16r; move K16r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K17l; move K17l before pvzI17; pose proof (proj2 pvzI17) as K17r; move K17r before pvzI17; clear pvzI17.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 38%nat => Z_to_bv 64 vz_38 | 55%nat => Z_to_bv 64 vz_55 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 38%nat => vz_38 | 55%nat => vz_55 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 69%nat. }
  assert (HR: regs_ok E PdkXN0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdkXN0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdkXN0.kn0).
  { unfold know_ok, PdkXN0.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV55l HV55r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PdkXN0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PdkXN0.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_33 + 0) <= bv_unsigned a < (vz_33 + 0) + 42) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PdkXN0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K12l K12r K14 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PdkXN0.ps0) with 0x39048 in Hms. change (SR.ps_regs PdkXN0.ps0) with (map (fun i => (i, nth i PdkXN0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PdkXN0.ps0) with PdkXN0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkXN0.regs0 PdkXN0.regs_out0 80 KS_dkXN0 KS_dkXN0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PdkXN0.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PdkXN0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkXN0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PdkXN0.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PdkXN0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PdkXN0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkXN0.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PdkXN0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkXN0.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PdkXN0.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
  split. { rewrite (BG.out_reg PdkXN0.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PdkXN0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkXN0.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PdkXN0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkXN0.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PdkXN0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K12l K12r K14 HV38l HV38r K16l K16r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K12l K12r K14 HV38l HV38r K16l K16r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PdkXN1 := LibSegBs_dkXN1_u.
Definition KS_dkXN1 : list nat := Eval vm_compute in (BG.kept_list 80 PdkXN1.regs0 PdkXN1.regs_out0).
Lemma KS_dkXN1_ok : BG.kept_ok 80 PdkXN1.regs0 PdkXN1.regs_out0 KS_dkXN1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dkXN1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 42) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + (V 38%nat)) -> getr R (reg 11) = Z_to_bv 64 (-1) -> getr R (reg 12) = Z_to_bv 64 (V 55%nat) ->
  140735332483312 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) ->
  4096 <= (V 33%nat) <= 140737488355286 -> L5.writable RSEGS M (V 33%nat) 42 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 42 <= ((V 2%nat) - 256)) -> L5.img_clear M 65536 754672 ->
  0 <= (V 38%nat) <= 1 -> 1 <= (V 55%nat) <= 36 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 42) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 42) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38e48 M) (st fx' R' 0x39048 M')
        /\ (forall x, In x KS_dkXN1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 1
        /\ getr R' (reg 10) = getr R (reg 13)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 (((V 33%nat) + (V 38%nat)) + 3)
        /\ bv_unsigned (getr R' (reg 14)) = (Z.land (bv_unsigned (getr R (reg 13))) 3)
        /\ getr R' (reg 15) = Z_to_bv 64 (V 55%nat)
        /\ getr R' (reg 16) = Z_to_bv 64 18446744073709551611
        /\ getr R' (reg 17) = Z_to_bv 64 1
        /\ L5.u8_at RSEGS M' (((V 33%nat) + (V 38%nat)) + 2) 48
        /\ L5.u8_at RSEGS M' (((V 33%nat) + (V 38%nat)) + 1) 46
        /\ L5.u8_at RSEGS M' ((V 33%nat) + (V 38%nat)) 48).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 G2 G8 G9 G11 G12 pvzI14 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 pvzI15 K13 K14 K15 pvzI16 pvzI17.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV55l; move HV55l before pvzI4; pose proof (proj2 pvzI4) as HV55r; move HV55r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV60l; move HV60l before pvzI5; pose proof (proj2 pvzI5) as HV60r; move HV60r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV61l; move HV61l before pvzI6; pose proof (proj2 pvzI6) as HV61r; move HV61r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV62l; move HV62l before pvzI7; pose proof (proj2 pvzI7) as HV62r; move HV62r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV63l; move HV63l before pvzI8; pose proof (proj2 pvzI8) as HV63r; move HV63r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV64l; move HV64l before pvzI9; pose proof (proj2 pvzI9) as HV64r; move HV64r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV65l; move HV65l before pvzI10; pose proof (proj2 pvzI10) as HV65r; move HV65r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV66l; move HV66l before pvzI11; pose proof (proj2 pvzI11) as HV66r; move HV66r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV67l; move HV67l before pvzI12; pose proof (proj2 pvzI12) as HV67r; move HV67r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV68l; move HV68l before pvzI13; pose proof (proj2 pvzI13) as HV68r; move HV68r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K0l; move K0l before pvzI14; pose proof (proj2 pvzI14) as K0r; move K0r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K12l; move K12l before pvzI15; pose proof (proj2 pvzI15) as K12r; move K12r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K16l; move K16l before pvzI16; pose proof (proj2 pvzI16) as K16r; move K16r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K17l; move K17l before pvzI17; pose proof (proj2 pvzI17) as K17r; move K17r before pvzI17; clear pvzI17.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 38%nat => Z_to_bv 64 vz_38 | 55%nat => Z_to_bv 64 vz_55 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 38%nat => vz_38 | 55%nat => vz_55 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 69%nat. }
  assert (HR: regs_ok E PdkXN1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdkXN1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdkXN1.kn0).
  { unfold know_ok, PdkXN1.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV55l HV55r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PdkXN1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PdkXN1.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_33 + 0) <= bv_unsigned a < (vz_33 + 0) + 42) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PdkXN1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K12l K12r K14 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PdkXN1.ps0) with 0x39048 in Hms. change (SR.ps_regs PdkXN1.ps0) with (map (fun i => (i, nth i PdkXN1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PdkXN1.ps0) with PdkXN1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkXN1.regs0 PdkXN1.regs_out0 80 KS_dkXN1 KS_dkXN1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PdkXN1.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PdkXN1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkXN1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PdkXN1.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PdkXN1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PdkXN1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkXN1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PdkXN1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkXN1.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PdkXN1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkXN1.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PdkXN1.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
  split. { rewrite (BG.out_reg PdkXN1.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PdkXN1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkXN1.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PdkXN1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkXN1.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PdkXN1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K12l K12r K14 HV38l HV38r K16l K16r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K12l K12r K14 HV38l HV38r K16l K16r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K12l K12r K14 HV38l HV38r K16l K16r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PdkXN2 := LibSegBs_dkXN2_u.
Definition KS_dkXN2 : list nat := Eval vm_compute in (BG.kept_list 80 PdkXN2.regs0 PdkXN2.regs_out0).
Lemma KS_dkXN2_ok : BG.kept_ok 80 PdkXN2.regs0 PdkXN2.regs_out0 KS_dkXN2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dkXN2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 42) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + (V 38%nat)) -> getr R (reg 11) = Z_to_bv 64 (-2) -> getr R (reg 12) = Z_to_bv 64 (V 55%nat) ->
  140735332483312 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) ->
  4096 <= (V 33%nat) <= 140737488355286 -> L5.writable RSEGS M (V 33%nat) 42 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 42 <= ((V 2%nat) - 256)) -> L5.img_clear M 65536 754672 ->
  0 <= (V 38%nat) <= 1 -> 1 <= (V 55%nat) <= 36 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 42) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 42) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38e48 M) (st fx' R' 0x39048 M')
        /\ (forall x, In x KS_dkXN2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 1
        /\ getr R' (reg 10) = getr R (reg 13)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 (((V 33%nat) + (V 38%nat)) + 4)
        /\ bv_unsigned (getr R' (reg 14)) = (Z.land (bv_unsigned (getr R (reg 13))) 3)
        /\ getr R' (reg 15) = Z_to_bv 64 (V 55%nat)
        /\ getr R' (reg 16) = Z_to_bv 64 18446744073709551611
        /\ getr R' (reg 17) = Z_to_bv 64 1
        /\ L5.u8_at RSEGS M' (((V 33%nat) + (V 38%nat)) + 3) 48
        /\ L5.u8_at RSEGS M' (((V 33%nat) + (V 38%nat)) + 2) 48
        /\ L5.u8_at RSEGS M' (((V 33%nat) + (V 38%nat)) + 1) 46
        /\ L5.u8_at RSEGS M' ((V 33%nat) + (V 38%nat)) 48).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 G2 G8 G9 G11 G12 pvzI14 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 pvzI15 K13 K14 K15 pvzI16 pvzI17.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV55l; move HV55l before pvzI4; pose proof (proj2 pvzI4) as HV55r; move HV55r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV60l; move HV60l before pvzI5; pose proof (proj2 pvzI5) as HV60r; move HV60r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV61l; move HV61l before pvzI6; pose proof (proj2 pvzI6) as HV61r; move HV61r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV62l; move HV62l before pvzI7; pose proof (proj2 pvzI7) as HV62r; move HV62r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV63l; move HV63l before pvzI8; pose proof (proj2 pvzI8) as HV63r; move HV63r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV64l; move HV64l before pvzI9; pose proof (proj2 pvzI9) as HV64r; move HV64r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV65l; move HV65l before pvzI10; pose proof (proj2 pvzI10) as HV65r; move HV65r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV66l; move HV66l before pvzI11; pose proof (proj2 pvzI11) as HV66r; move HV66r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV67l; move HV67l before pvzI12; pose proof (proj2 pvzI12) as HV67r; move HV67r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV68l; move HV68l before pvzI13; pose proof (proj2 pvzI13) as HV68r; move HV68r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K0l; move K0l before pvzI14; pose proof (proj2 pvzI14) as K0r; move K0r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K12l; move K12l before pvzI15; pose proof (proj2 pvzI15) as K12r; move K12r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K16l; move K16l before pvzI16; pose proof (proj2 pvzI16) as K16r; move K16r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K17l; move K17l before pvzI17; pose proof (proj2 pvzI17) as K17r; move K17r before pvzI17; clear pvzI17.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 38%nat => Z_to_bv 64 vz_38 | 55%nat => Z_to_bv 64 vz_55 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 38%nat => vz_38 | 55%nat => vz_55 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 69%nat. }
  assert (HR: regs_ok E PdkXN2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdkXN2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdkXN2.kn0).
  { unfold know_ok, PdkXN2.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV55l HV55r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PdkXN2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PdkXN2.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_33 + 0) <= bv_unsigned a < (vz_33 + 0) + 42) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PdkXN2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K12l K12r K14 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PdkXN2.ps0) with 0x39048 in Hms. change (SR.ps_regs PdkXN2.ps0) with (map (fun i => (i, nth i PdkXN2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PdkXN2.ps0) with PdkXN2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkXN2.regs0 PdkXN2.regs_out0 80 KS_dkXN2 KS_dkXN2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PdkXN2.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PdkXN2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkXN2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PdkXN2.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PdkXN2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PdkXN2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkXN2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PdkXN2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkXN2.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PdkXN2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkXN2.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PdkXN2.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
  split. { rewrite (BG.out_reg PdkXN2.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PdkXN2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkXN2.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PdkXN2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkXN2.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PdkXN2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K12l K12r K14 HV38l HV38r K16l K16r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K12l K12r K14 HV38l HV38r K16l K16r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K12l K12r K14 HV38l HV38r K16l K16r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K12l K12r K14 HV38l HV38r K16l K16r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PdkXN3 := LibSegBs_dkXN3_u.
Definition KS_dkXN3 : list nat := Eval vm_compute in (BG.kept_list 80 PdkXN3.regs0 PdkXN3.regs_out0).
Lemma KS_dkXN3_ok : BG.kept_ok 80 PdkXN3.regs0 PdkXN3.regs_out0 KS_dkXN3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dkXN3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 42) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + (V 38%nat)) -> getr R (reg 11) = Z_to_bv 64 (-3) -> getr R (reg 12) = Z_to_bv 64 (V 55%nat) ->
  140735332483312 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) ->
  4096 <= (V 33%nat) <= 140737488355286 -> L5.writable RSEGS M (V 33%nat) 42 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 42 <= ((V 2%nat) - 256)) -> L5.img_clear M 65536 754672 ->
  0 <= (V 38%nat) <= 1 -> 1 <= (V 55%nat) <= 36 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 42) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 42) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38e48 M) (st fx' R' 0x39048 M')
        /\ (forall x, In x KS_dkXN3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 1
        /\ getr R' (reg 10) = getr R (reg 13)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 (((V 33%nat) + (V 38%nat)) + 5)
        /\ bv_unsigned (getr R' (reg 14)) = (Z.land (bv_unsigned (getr R (reg 13))) 3)
        /\ getr R' (reg 15) = Z_to_bv 64 (V 55%nat)
        /\ getr R' (reg 16) = Z_to_bv 64 18446744073709551611
        /\ getr R' (reg 17) = Z_to_bv 64 1
        /\ L5.u8_at RSEGS M' (((V 33%nat) + (V 38%nat)) + 4) 48
        /\ L5.u8_at RSEGS M' (((V 33%nat) + (V 38%nat)) + 3) 48
        /\ L5.u8_at RSEGS M' (((V 33%nat) + (V 38%nat)) + 2) 48
        /\ L5.u8_at RSEGS M' (((V 33%nat) + (V 38%nat)) + 1) 46
        /\ L5.u8_at RSEGS M' ((V 33%nat) + (V 38%nat)) 48).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 G2 G8 G9 G11 G12 pvzI14 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 pvzI15 K13 K14 K15 pvzI16 pvzI17.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV55l; move HV55l before pvzI4; pose proof (proj2 pvzI4) as HV55r; move HV55r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV60l; move HV60l before pvzI5; pose proof (proj2 pvzI5) as HV60r; move HV60r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV61l; move HV61l before pvzI6; pose proof (proj2 pvzI6) as HV61r; move HV61r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV62l; move HV62l before pvzI7; pose proof (proj2 pvzI7) as HV62r; move HV62r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV63l; move HV63l before pvzI8; pose proof (proj2 pvzI8) as HV63r; move HV63r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV64l; move HV64l before pvzI9; pose proof (proj2 pvzI9) as HV64r; move HV64r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV65l; move HV65l before pvzI10; pose proof (proj2 pvzI10) as HV65r; move HV65r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV66l; move HV66l before pvzI11; pose proof (proj2 pvzI11) as HV66r; move HV66r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV67l; move HV67l before pvzI12; pose proof (proj2 pvzI12) as HV67r; move HV67r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV68l; move HV68l before pvzI13; pose proof (proj2 pvzI13) as HV68r; move HV68r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K0l; move K0l before pvzI14; pose proof (proj2 pvzI14) as K0r; move K0r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K12l; move K12l before pvzI15; pose proof (proj2 pvzI15) as K12r; move K12r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K16l; move K16l before pvzI16; pose proof (proj2 pvzI16) as K16r; move K16r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K17l; move K17l before pvzI17; pose proof (proj2 pvzI17) as K17r; move K17r before pvzI17; clear pvzI17.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 38%nat => Z_to_bv 64 vz_38 | 55%nat => Z_to_bv 64 vz_55 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 38%nat => vz_38 | 55%nat => vz_55 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 69%nat. }
  assert (HR: regs_ok E PdkXN3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdkXN3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdkXN3.kn0).
  { unfold know_ok, PdkXN3.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV55l HV55r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PdkXN3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PdkXN3.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_33 + 0) <= bv_unsigned a < (vz_33 + 0) + 42) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PdkXN3.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K12l K12r K14 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PdkXN3.ps0) with 0x39048 in Hms. change (SR.ps_regs PdkXN3.ps0) with (map (fun i => (i, nth i PdkXN3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PdkXN3.ps0) with PdkXN3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkXN3.regs0 PdkXN3.regs_out0 80 KS_dkXN3 KS_dkXN3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PdkXN3.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PdkXN3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkXN3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PdkXN3.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PdkXN3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PdkXN3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkXN3.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PdkXN3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkXN3.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PdkXN3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkXN3.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PdkXN3.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
  split. { rewrite (BG.out_reg PdkXN3.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PdkXN3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkXN3.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PdkXN3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkXN3.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PdkXN3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K12l K12r K14 HV38l HV38r K16l K16r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K12l K12r K14 HV38l HV38r K16l K16r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K12l K12r K14 HV38l HV38r K16l K16r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K12l K12r K14 HV38l HV38r K16l K16r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K12l K12r K14 HV38l HV38r K16l K16r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PdkXN4 := LibSegBs_dkXN4_u.
Definition KS_dkXN4 : list nat := Eval vm_compute in (BG.kept_list 80 PdkXN4.regs0 PdkXN4.regs_out0).
Lemma KS_dkXN4_ok : BG.kept_ok 80 PdkXN4.regs0 PdkXN4.regs_out0 KS_dkXN4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dkXN4_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 42) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + (V 38%nat)) -> getr R (reg 11) = Z_to_bv 64 (-4) -> getr R (reg 12) = Z_to_bv 64 (V 55%nat) ->
  140735332483312 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) ->
  4096 <= (V 33%nat) <= 140737488355286 -> L5.writable RSEGS M (V 33%nat) 42 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 42 <= ((V 2%nat) - 256)) -> L5.img_clear M 65536 754672 ->
  0 <= (V 38%nat) <= 1 -> 1 <= (V 55%nat) <= 36 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 42) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 42) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38e48 M) (st fx' R' 0x39048 M')
        /\ (forall x, In x KS_dkXN4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 1
        /\ getr R' (reg 10) = getr R (reg 13)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 (((V 33%nat) + (V 38%nat)) + 6)
        /\ bv_unsigned (getr R' (reg 14)) = (Z.land (bv_unsigned (getr R (reg 13))) 3)
        /\ getr R' (reg 15) = Z_to_bv 64 (V 55%nat)
        /\ getr R' (reg 16) = Z_to_bv 64 18446744073709551611
        /\ getr R' (reg 17) = Z_to_bv 64 1
        /\ L5.u8_at RSEGS M' (((V 33%nat) + (V 38%nat)) + 5) 48
        /\ L5.u8_at RSEGS M' (((V 33%nat) + (V 38%nat)) + 4) 48
        /\ L5.u8_at RSEGS M' (((V 33%nat) + (V 38%nat)) + 3) 48
        /\ L5.u8_at RSEGS M' (((V 33%nat) + (V 38%nat)) + 2) 48
        /\ L5.u8_at RSEGS M' (((V 33%nat) + (V 38%nat)) + 1) 46
        /\ L5.u8_at RSEGS M' ((V 33%nat) + (V 38%nat)) 48).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 G2 G8 G9 G11 G12 pvzI14 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 pvzI15 K13 K14 K15 pvzI16 pvzI17.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV55l; move HV55l before pvzI4; pose proof (proj2 pvzI4) as HV55r; move HV55r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV60l; move HV60l before pvzI5; pose proof (proj2 pvzI5) as HV60r; move HV60r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV61l; move HV61l before pvzI6; pose proof (proj2 pvzI6) as HV61r; move HV61r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV62l; move HV62l before pvzI7; pose proof (proj2 pvzI7) as HV62r; move HV62r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV63l; move HV63l before pvzI8; pose proof (proj2 pvzI8) as HV63r; move HV63r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV64l; move HV64l before pvzI9; pose proof (proj2 pvzI9) as HV64r; move HV64r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV65l; move HV65l before pvzI10; pose proof (proj2 pvzI10) as HV65r; move HV65r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV66l; move HV66l before pvzI11; pose proof (proj2 pvzI11) as HV66r; move HV66r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV67l; move HV67l before pvzI12; pose proof (proj2 pvzI12) as HV67r; move HV67r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV68l; move HV68l before pvzI13; pose proof (proj2 pvzI13) as HV68r; move HV68r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K0l; move K0l before pvzI14; pose proof (proj2 pvzI14) as K0r; move K0r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K12l; move K12l before pvzI15; pose proof (proj2 pvzI15) as K12r; move K12r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K16l; move K16l before pvzI16; pose proof (proj2 pvzI16) as K16r; move K16r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K17l; move K17l before pvzI17; pose proof (proj2 pvzI17) as K17r; move K17r before pvzI17; clear pvzI17.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 38%nat => Z_to_bv 64 vz_38 | 55%nat => Z_to_bv 64 vz_55 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 38%nat => vz_38 | 55%nat => vz_55 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 69%nat. }
  assert (HR: regs_ok E PdkXN4.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdkXN4.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdkXN4.kn0).
  { unfold know_ok, PdkXN4.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV55l HV55r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PdkXN4.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PdkXN4.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_33 + 0) <= bv_unsigned a < (vz_33 + 0) + 42) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PdkXN4.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K12l K12r K14 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PdkXN4.ps0) with 0x39048 in Hms. change (SR.ps_regs PdkXN4.ps0) with (map (fun i => (i, nth i PdkXN4.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PdkXN4.ps0) with PdkXN4.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkXN4.regs0 PdkXN4.regs_out0 80 KS_dkXN4 KS_dkXN4_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PdkXN4.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PdkXN4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkXN4.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PdkXN4.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PdkXN4.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PdkXN4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkXN4.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PdkXN4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkXN4.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PdkXN4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkXN4.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PdkXN4.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
  split. { rewrite (BG.out_reg PdkXN4.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PdkXN4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkXN4.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PdkXN4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkXN4.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PdkXN4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K12l K12r K14 HV38l HV38r K16l K16r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K12l K12r K14 HV38l HV38r K16l K16r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K12l K12r K14 HV38l HV38r K16l K16r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K12l K12r K14 HV38l HV38r K16l K16r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K12l K12r K14 HV38l HV38r K16l K16r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K12l K12r K14 HV38l HV38r K16l K16r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PdkXN5 := LibSegBs_dkXN5_u.
Definition KS_dkXN5 : list nat := Eval vm_compute in (BG.kept_list 80 PdkXN5.regs0 PdkXN5.regs_out0).
Lemma KS_dkXN5_ok : BG.kept_ok 80 PdkXN5.regs0 PdkXN5.regs_out0 KS_dkXN5 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dkXN5_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 42) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + (V 38%nat)) -> getr R (reg 11) = Z_to_bv 64 (-5) -> getr R (reg 12) = Z_to_bv 64 (V 55%nat) ->
  140735332483312 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) ->
  4096 <= (V 33%nat) <= 140737488355286 -> L5.writable RSEGS M (V 33%nat) 42 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 42 <= ((V 2%nat) - 256)) -> L5.img_clear M 65536 754672 ->
  0 <= (V 38%nat) <= 1 -> 1 <= (V 55%nat) <= 36 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 42) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 42) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38e48 M) (st fx' R' 0x39048 M')
        /\ (forall x, In x KS_dkXN5 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 1
        /\ getr R' (reg 10) = getr R (reg 13)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 (((V 33%nat) + (V 38%nat)) + 7)
        /\ bv_unsigned (getr R' (reg 14)) = (Z.land (bv_unsigned (getr R (reg 13))) 3)
        /\ getr R' (reg 15) = Z_to_bv 64 (V 55%nat)
        /\ getr R' (reg 16) = Z_to_bv 64 18446744073709551611
        /\ getr R' (reg 17) = Z_to_bv 64 1
        /\ L5.u8_at RSEGS M' (((V 33%nat) + (V 38%nat)) + 6) 48
        /\ L5.u8_at RSEGS M' (((V 33%nat) + (V 38%nat)) + 5) 48
        /\ L5.u8_at RSEGS M' (((V 33%nat) + (V 38%nat)) + 4) 48
        /\ L5.u8_at RSEGS M' (((V 33%nat) + (V 38%nat)) + 3) 48
        /\ L5.u8_at RSEGS M' (((V 33%nat) + (V 38%nat)) + 2) 48
        /\ L5.u8_at RSEGS M' (((V 33%nat) + (V 38%nat)) + 1) 46
        /\ L5.u8_at RSEGS M' ((V 33%nat) + (V 38%nat)) 48).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 G2 G8 G9 G11 G12 pvzI14 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 pvzI15 K13 K14 K15 pvzI16 pvzI17.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV55l; move HV55l before pvzI4; pose proof (proj2 pvzI4) as HV55r; move HV55r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV60l; move HV60l before pvzI5; pose proof (proj2 pvzI5) as HV60r; move HV60r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV61l; move HV61l before pvzI6; pose proof (proj2 pvzI6) as HV61r; move HV61r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV62l; move HV62l before pvzI7; pose proof (proj2 pvzI7) as HV62r; move HV62r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV63l; move HV63l before pvzI8; pose proof (proj2 pvzI8) as HV63r; move HV63r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV64l; move HV64l before pvzI9; pose proof (proj2 pvzI9) as HV64r; move HV64r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV65l; move HV65l before pvzI10; pose proof (proj2 pvzI10) as HV65r; move HV65r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV66l; move HV66l before pvzI11; pose proof (proj2 pvzI11) as HV66r; move HV66r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV67l; move HV67l before pvzI12; pose proof (proj2 pvzI12) as HV67r; move HV67r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV68l; move HV68l before pvzI13; pose proof (proj2 pvzI13) as HV68r; move HV68r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K0l; move K0l before pvzI14; pose proof (proj2 pvzI14) as K0r; move K0r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K12l; move K12l before pvzI15; pose proof (proj2 pvzI15) as K12r; move K12r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K16l; move K16l before pvzI16; pose proof (proj2 pvzI16) as K16r; move K16r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K17l; move K17l before pvzI17; pose proof (proj2 pvzI17) as K17r; move K17r before pvzI17; clear pvzI17.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 38%nat => Z_to_bv 64 vz_38 | 55%nat => Z_to_bv 64 vz_55 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 38%nat => vz_38 | 55%nat => vz_55 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 69%nat. }
  assert (HR: regs_ok E PdkXN5.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdkXN5.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdkXN5.kn0).
  { unfold know_ok, PdkXN5.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV55l HV55r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PdkXN5.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PdkXN5.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_33 + 0) <= bv_unsigned a < (vz_33 + 0) + 42) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PdkXN5.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K12l K12r K14) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K12l K12r K14 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PdkXN5.ps0) with 0x39048 in Hms. change (SR.ps_regs PdkXN5.ps0) with (map (fun i => (i, nth i PdkXN5.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PdkXN5.ps0) with PdkXN5.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkXN5.regs0 PdkXN5.regs_out0 80 KS_dkXN5 KS_dkXN5_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PdkXN5.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PdkXN5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkXN5.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PdkXN5.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PdkXN5.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PdkXN5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkXN5.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PdkXN5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkXN5.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PdkXN5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkXN5.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PdkXN5.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
  split. { rewrite (BG.out_reg PdkXN5.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PdkXN5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkXN5.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PdkXN5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkXN5.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PdkXN5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K12l K12r K14 HV38l HV38r K16l K16r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K12l K12r K14 HV38l HV38r K16l K16r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K12l K12r K14 HV38l HV38r K16l K16r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K12l K12r K14 HV38l HV38r K16l K16r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K12l K12r K14 HV38l HV38r K16l K16r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K12l K12r K14 HV38l HV38r K16l K16r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K12l K12r K14 HV38l HV38r K16l K16r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

End PNSDXP.
