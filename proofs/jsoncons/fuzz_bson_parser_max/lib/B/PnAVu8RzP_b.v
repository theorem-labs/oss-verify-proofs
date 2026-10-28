(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BigLinkZA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0PlanKit_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanPlanCore
     BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require LibSegBa_avzA_b LibSegBa_avzAn_b LibSegBa_avzS_b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PMAVRZ.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).

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
Module PavzA := LibSegBa_avzA_b.
Definition KS_avzA_0 : list nat := Eval vm_compute in (BG.kept_list 70 PavzA.regs0 PavzA.regs_out0).
Lemma KS_avzA_0_ok : BG.kept_ok 70 PavzA.regs0 PavzA.regs_out0 KS_avzA_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avzA_1 : list nat := Eval vm_compute in (BG.kept_list 70 PavzA.regs0 PavzA.regs_out1).
Lemma KS_avzA_1_ok : BG.kept_ok 70 PavzA.regs0 PavzA.regs_out1 KS_avzA_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avzA_2 : list nat := Eval vm_compute in (BG.kept_list 70 PavzA.regs0 PavzA.regs_out2).
Lemma KS_avzA_2_ok : BG.kept_ok 70 PavzA.regs0 PavzA.regs_out2 KS_avzA_2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avzA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 37%nat) -> getr R (reg 11) = Z_to_bv 64 (V 43%nat) ->
  L5.img_clear M 1249280 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487184 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 16) 16 -> 6905856 <= (V 37%nat) <= 140737488355304 -> aligned (V 37%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 37%nat) 24 -> (((V 2%nat) - 16) + 16 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 16)) ->
  L5.u64_at RSEGS M (V 37%nat) (V 40%nat) -> L5.u64_at RSEGS M ((V 37%nat) + 8) ((V 40%nat) + (V 41%nat)) -> 0 <= (V 41%nat) <= 134217728 -> 0 <= (V 43%nat) <= 134217728 ->
  4096 <= (V 40%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 16) -> ~ (((V 37%nat) + 8) <= bv_unsigned a < ((V 37%nat) + 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 16) <= i < ((V 2%nat) - 16) + 16) -> ~ (((V 37%nat) + 8) <= i < ((V 37%nat) + 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb5764 M) (st fx' R' 0xb5800 M')
        /\ (forall x, In x KS_avzA_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 (((-1) * (V 41%nat)) + (V 43%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 15) = getr R (reg 15)
        /\ (V 41%nat) < (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))
        /\ L5.u64_at RSEGS M' ((V 37%nat) + 8) ((V 40%nat) + (V 41%nat)))
      \/ (msteps RSEGS (st fx R 0xb5764 M) (st fx' R' 0xb592c M')
        /\ (forall x, In x KS_avzA_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + (V 43%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 15) = getr R (reg 15)
        /\ L5.u64_at RSEGS M' ((V 37%nat) + 8) ((V 40%nat) + (V 41%nat))
        /\ (V 43%nat) < (V 41%nat)
        /\ (V 43%nat) <= (V 41%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))
      \/ (msteps RSEGS (st fx R 0xb5764 M) (st fx' R' 0xb57ec M')
        /\ (forall x, In x KS_avzA_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 12) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 15) = getr R (reg 15)
        /\ (V 41%nat) <= (V 43%nat)
        /\ (V 43%nat) <= (V 41%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))
        /\ L5.u64_at RSEGS M' ((V 37%nat) + 8) ((V 40%nat) + (V 41%nat)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G10 G11 K0 K1 K2 pvzI6 K4 K5 pvzI7 K7 K8 K9 K10 K11 K12 K13 pvzI8 pvzI9 pvzI10.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV37l; move HV37l before pvzI2; pose proof (proj2 pvzI2) as HV37r; move HV37r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV40l; move HV40l before pvzI3; pose proof (proj2 pvzI3) as HV40r; move HV40r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV41l; move HV41l before pvzI4; pose proof (proj2 pvzI4) as HV41r; move HV41r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV43l; move HV43l before pvzI5; pose proof (proj2 pvzI5) as HV43r; move HV43r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K6l; move K6l before pvzI7; pose proof (proj2 pvzI7) as K6r; move K6r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K14l; move K14l before pvzI8; pose proof (proj2 pvzI8) as K14r; move K14r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K15l; move K15l before pvzI9; pose proof (proj2 pvzI9) as K15r; move K15r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K16l; move K16l before pvzI10; pose proof (proj2 pvzI10) as K16r; move K16r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_43 := V 43%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 37%nat => Z_to_bv 64 vz_37 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 43%nat => Z_to_bv 64 vz_43 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 37%nat => vz_37 | 40%nat => vz_40 | 41%nat => vz_41 | 43%nat => vz_43 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E PavzA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavzA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavzA.kn0).
  { unfold know_ok, PavzA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear - HV40l HV40r K16l K16r) | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear - HV40l HV40r K16l K16r HV41l HV41r K14l K14r) | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K15l K15r) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavzA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavzA.NX0 with 70%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 16) <= bv_unsigned a < (vz_2 - 16) + 16) -> ~ ((vz_37 + 8) <= bv_unsigned a < (vz_37 + 8) + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PavzA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K11 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk' ZA Hag ltac:(clear) | clear - HV37l HV37r K6l K6r K8 K11 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PavzA.ps0) with 0xb5800 in Hms. change (SR.ps_regs PavzA.ps0) with (map (fun i => (i, nth i PavzA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavzA.ps0) with PavzA.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavzA.regs0 PavzA.regs_out0 70 KS_avzA_0 KS_avzA_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavzA.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavzA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavzA.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavzA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavzA.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PavzA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavzA.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PavzA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavzA.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PavzA.regs_out0]. rewrite (BG.edenot_kept 70 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K16l K16r HV41l HV41r K14l K14r) | clear; lia].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. left.
    change (SR.ps_pc PavzA.ps1) with 0xb592c in Hms. change (SR.ps_regs PavzA.ps1) with (map (fun i => (i, nth i PavzA.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavzA.ps1) with PavzA.cells1 in Hcells. unfold PavzA.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavzA.regs0 PavzA.regs_out1 70 KS_avzA_1 KS_avzA_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavzA.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavzA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavzA.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PavzA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavzA.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PavzA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavzA.regs_out1 E' R' 14 Hregs) by (clear; lia). cbn [nth PavzA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavzA.regs_out1 E' R' 15 Hregs) by (clear; lia). cbn [nth PavzA.regs_out1]. rewrite (BG.edenot_kept 70 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K16l K16r HV41l HV41r K14l K14r) | clear; lia]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right.
    change (SR.ps_pc PavzA.ps2) with 0xb57ec in Hms. change (SR.ps_regs PavzA.ps2) with (map (fun i => (i, nth i PavzA.regs_out2 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavzA.ps2) with PavzA.cells2 in Hcells. unfold PavzA.cells2 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavzA.regs0 PavzA.regs_out2 70 KS_avzA_2 KS_avzA_2_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavzA.regs_out2 E' R' 12 Hregs) by (clear; lia). cbn [nth PavzA.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavzA.regs_out2 E' R' 13 Hregs) by (clear; lia). cbn [nth PavzA.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavzA.regs_out2 E' R' 14 Hregs) by (clear; lia). cbn [nth PavzA.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavzA.regs_out2 E' R' 15 Hregs) by (clear; lia). cbn [nth PavzA.regs_out2]. rewrite (BG.edenot_kept 70 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K16l K16r HV41l HV41r K14l K14r) | clear; lia].
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.

Module PavzAn := LibSegBa_avzAn_b.
Definition KS_avzAn_0 : list nat := Eval vm_compute in (BG.kept_list 70 PavzAn.regs0 PavzAn.regs_out0).
Lemma KS_avzAn_0_ok : BG.kept_ok 70 PavzAn.regs0 PavzAn.regs_out0 KS_avzAn_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avzAn_1 : list nat := Eval vm_compute in (BG.kept_list 70 PavzAn.regs0 PavzAn.regs_out1).
Lemma KS_avzAn_1_ok : BG.kept_ok 70 PavzAn.regs0 PavzAn.regs_out1 KS_avzAn_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avzAn_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 37%nat) -> getr R (reg 11) = Z_to_bv 64 (V 43%nat) ->
  L5.img_clear M 1249280 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487184 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 16) 16 -> 6905856 <= (V 37%nat) <= 140737488355304 -> aligned (V 37%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 37%nat) 24 -> (((V 2%nat) - 16) + 16 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 16)) ->
  L5.u64_at RSEGS M (V 37%nat) (V 40%nat) -> L5.u64_at RSEGS M ((V 37%nat) + 8) ((V 40%nat) + (V 41%nat)) -> 0 <= (V 43%nat) <= 134217728 -> 0 <= (V 40%nat) <= 0 ->
  0 <= (V 41%nat) <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 16) -> ~ (((V 37%nat) + 8) <= bv_unsigned a < ((V 37%nat) + 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 16) <= i < ((V 2%nat) - 16) + 16) -> ~ (((V 37%nat) + 8) <= i < ((V 37%nat) + 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb5764 M) (st fx' R' 0xb5800 M')
        /\ (forall x, In x KS_avzAn_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 15) = getr R (reg 15)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))
        /\ L5.u64_at RSEGS M' ((V 37%nat) + 8) ((V 40%nat) + (V 41%nat))
        /\ 0 < (V 43%nat))
      \/ (msteps RSEGS (st fx R 0xb5764 M) (st fx' R' 0xb57ec M')
        /\ (forall x, In x KS_avzAn_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 15) = getr R (reg 15)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))
        /\ L5.u64_at RSEGS M' ((V 37%nat) + 8) ((V 40%nat) + (V 41%nat))
        /\ (V 43%nat) = 0)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G10 G11 K0 K1 K2 pvzI6 K4 K5 pvzI7 K7 K8 K9 K10 K11 K12 K13 pvzI8 pvzI9 pvzI10.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV37l; move HV37l before pvzI2; pose proof (proj2 pvzI2) as HV37r; move HV37r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV40l; move HV40l before pvzI3; pose proof (proj2 pvzI3) as HV40r; move HV40r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV41l; move HV41l before pvzI4; pose proof (proj2 pvzI4) as HV41r; move HV41r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV43l; move HV43l before pvzI5; pose proof (proj2 pvzI5) as HV43r; move HV43r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K6l; move K6l before pvzI7; pose proof (proj2 pvzI7) as K6r; move K6r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K14l; move K14l before pvzI8; pose proof (proj2 pvzI8) as K14r; move K14r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K15l; move K15l before pvzI9; pose proof (proj2 pvzI9) as K15r; move K15r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K16l; move K16l before pvzI10; pose proof (proj2 pvzI10) as K16r; move K16r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_43 := V 43%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 37%nat => Z_to_bv 64 vz_37 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 43%nat => Z_to_bv 64 vz_43 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 37%nat => vz_37 | 40%nat => vz_40 | 41%nat => vz_41 | 43%nat => vz_43 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E PavzAn.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavzAn.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavzAn.kn0).
  { unfold know_ok, PavzAn.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear - HV40l HV40r K15l K15r) | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear - HV40l HV40r K15l K15r HV41l HV41r K16l K16r) | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K15l K15r) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavzAn.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavzAn.NX0 with 70%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 16) <= bv_unsigned a < (vz_2 - 16) + 16) -> ~ ((vz_37 + 8) <= bv_unsigned a < (vz_37 + 8) + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PavzAn.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K11 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk' ZA Hag ltac:(clear) | clear - HV37l HV37r K6l K6r K8 K11 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PavzAn.ps0) with 0xb5800 in Hms. change (SR.ps_regs PavzAn.ps0) with (map (fun i => (i, nth i PavzAn.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavzAn.ps0) with PavzAn.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavzAn.regs0 PavzAn.regs_out0 70 KS_avzAn_0 KS_avzAn_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavzAn.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavzAn.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavzAn.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavzAn.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavzAn.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PavzAn.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavzAn.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PavzAn.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavzAn.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PavzAn.regs_out0]. rewrite (BG.edenot_kept 70 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K15l K15r HV41l HV41r K16l K16r) | clear; lia]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right.
    change (SR.ps_pc PavzAn.ps1) with 0xb57ec in Hms. change (SR.ps_regs PavzAn.ps1) with (map (fun i => (i, nth i PavzAn.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavzAn.ps1) with PavzAn.cells1 in Hcells. unfold PavzAn.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavzAn.regs0 PavzAn.regs_out1 70 KS_avzAn_1 KS_avzAn_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavzAn.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PavzAn.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavzAn.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PavzAn.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavzAn.regs_out1 E' R' 14 Hregs) by (clear; lia). cbn [nth PavzAn.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavzAn.regs_out1 E' R' 15 Hregs) by (clear; lia). cbn [nth PavzAn.regs_out1]. rewrite (BG.edenot_kept 70 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K15l K15r HV41l HV41r K16l K16r) | clear; lia]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear - HV43l HV43r K14l K14r; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.

Module PavzS := LibSegBa_avzS_b.
Definition KS_avzS : list nat := Eval vm_compute in (BG.kept_list 70 PavzS.regs0 PavzS.regs_out0).
Lemma KS_avzS_ok : BG.kept_ok 70 PavzS.regs0 PavzS.regs_out0 KS_avzS = true. Proof. vm_compute. reflexivity. Qed.
Lemma avzS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 37%nat) -> getr R (reg 11) = Z_to_bv 64 ((V 40%nat) + (V 43%nat)) -> getr R (reg 12) = Z_to_bv 64 1 -> getr R (reg 13) = Z_to_bv 64 0 -> getr R (reg 14) = Z_to_bv 64 0 ->
  L5.img_clear M 1249280 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487184 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 16) 16 -> 6905856 <= (V 37%nat) <= 140737488355304 -> aligned (V 37%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 37%nat) 24 -> (((V 2%nat) - 16) + 16 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 16)) ->
  L5.u64_at RSEGS M (V 37%nat) (V 40%nat) -> L5.u64_at RSEGS M ((V 37%nat) + 8) ((V 40%nat) + (V 41%nat)) -> 0 <= (V 41%nat) <= 134217728 -> 0 <= (V 43%nat) <= 134217728 ->
  4096 <= (V 40%nat) <= 140737488355328 -> (V 43%nat) < (V 41%nat) -> (V 43%nat) <= (V 41%nat) -> 1 <= (((((V 40%nat) + (V 43%nat)) mod 2 ^ 64) - (((V 40%nat) + (V 41%nat)) mod 2 ^ 64)) mod 2 ^ 64) ->
  ((((18446744073709551615 * (V 40%nat)) mod 2 ^ 64) + ((18446744073709551615 * (V 41%nat)) mod 2 ^ 64)) mod 2 ^ 64) < ((((18446744073709551615 * (V 41%nat)) mod 2 ^ 64) + (V 43%nat)) mod 2 ^ 64) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 16) -> ~ (((V 37%nat) + 8) <= bv_unsigned a < ((V 37%nat) + 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 16) <= i < ((V 2%nat) - 16) + 16) -> ~ (((V 37%nat) + 8) <= i < ((V 37%nat) + 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb592c M) (st fx' R' 0xabc48 M')
        /\ (forall x, In x KS_avzS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 40%nat) + (V 41%nat))
        /\ getr R' (reg 15) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 16) = Z_to_bv 64 (((-1) * (V 40%nat)) - (V 41%nat))
        /\ getr R' (reg 17) = Z_to_bv 64 (((-1) * (V 41%nat)) + (V 43%nat))
        /\ L5.u64_at RSEGS M' ((V 37%nat) + 8) ((V 40%nat) + (V 43%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G10 G11 G12 G13 G14 K0 K1 K2 pvzI6 K4 K5 pvzI7 K7 K8 K9 K10 K11 K12 K13 pvzI8 pvzI9 pvzI10 K17 K18 K19 K20.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV37l; move HV37l before pvzI2; pose proof (proj2 pvzI2) as HV37r; move HV37r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV40l; move HV40l before pvzI3; pose proof (proj2 pvzI3) as HV40r; move HV40r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV41l; move HV41l before pvzI4; pose proof (proj2 pvzI4) as HV41r; move HV41r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV43l; move HV43l before pvzI5; pose proof (proj2 pvzI5) as HV43r; move HV43r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K6l; move K6l before pvzI7; pose proof (proj2 pvzI7) as K6r; move K6r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K14l; move K14l before pvzI8; pose proof (proj2 pvzI8) as K14r; move K14r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K15l; move K15l before pvzI9; pose proof (proj2 pvzI9) as K15r; move K15r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K16l; move K16l before pvzI10; pose proof (proj2 pvzI10) as K16r; move K16r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_43 := V 43%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 37%nat => Z_to_bv 64 vz_37 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 43%nat => Z_to_bv 64 vz_43 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 37%nat => vz_37 | 40%nat => vz_40 | 41%nat => vz_41 | 43%nat => vz_43 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E PavzS.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavzS.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavzS.kn0).
  { unfold know_ok, PavzS.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear - HV40l HV40r K16l K16r) | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear - HV40l HV40r K16l K16r HV41l HV41r K14l K14r) | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K15l K15r) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | generalize K17; match goal with |- context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y) end; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | generalize K18; match goal with |- context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y) end; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | generalize K19; match goal with |- context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y) end; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | generalize K20; match goal with |- context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y) end; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavzS.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavzS.NX0 with 70%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 16) <= bv_unsigned a < (vz_2 - 16) + 16) -> ~ ((vz_37 + 8) <= bv_unsigned a < (vz_37 + 8) + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PavzS.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K11 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk' ZA Hag ltac:(clear) | clear - HV37l HV37r K6l K6r K8 K11 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PavzS.ps0) with 0xabc48 in Hms. change (SR.ps_regs PavzS.ps0) with (map (fun i => (i, nth i PavzS.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PavzS.ps0) with PavzS.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PavzS.regs0 PavzS.regs_out0 70 KS_avzS KS_avzS_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PavzS.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavzS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavzS.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavzS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavzS.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PavzS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavzS.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PavzS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavzS.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PavzS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavzS.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PavzS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K16l K16r HV43l HV43r K15l K15r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.
End PMAVRZ.
