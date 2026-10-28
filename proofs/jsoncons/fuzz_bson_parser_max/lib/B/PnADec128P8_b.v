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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require LibSegBa_adkYIa_b LibSegBa_adkYIb_b LibSegBa_adkYIc_b LibSegBa_adkYId_b LibSegBa_adkYNa_b LibSegBa_adkYNb_b LibSegBa_adkYNc_b LibSegBa_adkYNd_b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNADP8.
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
Module PadkYIa := LibSegBa_adkYIa_b.
Definition KS_adkYIa : list nat := Eval vm_compute in (BG.kept_list 80 PadkYIa.regs0 PadkYIa.regs_out0).
Lemma KS_adkYIa_ok : BG.kept_ok 80 PadkYIa.regs0 PadkYIa.regs_out0 KS_adkYIa = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma adkYIa_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (V 34%nat) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 1249280 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5.writable RSEGS M ((V 2%nat) - 320) 64 -> 4096 <= (V 50%nat) <= 140737488354816 ->
  4096 <= (V 33%nat) <= 140737488355280 -> 4096 <= (V 34%nat) <= 140737488355312 -> L5.img_clear M 6759136 6759144 -> L5.writable RSEGS M 6759136 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 320) <= bv_unsigned a < ((V 2%nat) - 320) + 64) -> ~ ((0 + 6759137) <= bv_unsigned a < (0 + 6759137) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 320) <= i < ((V 2%nat) - 320) + 64) -> ~ ((0 + 6759137) <= i < (0 + 6759137) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3fac M) (st fx' R' 0x6336c M')
        /\ (forall x, In x KS_adkYIa -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 729728
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 320)
        /\ getr R' (reg 8) = Z_to_bv 64 145632
        /\ getr R' (reg 10) = Z_to_bv 64 145632
        /\ getr R' (reg 11) = Z_to_bv 64 1309752
        /\ getr R' (reg 12) = Z_to_bv 64 2
        /\ getr R' (reg 18) = Z_to_bv 64 6759112
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 312) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 272) (V 2%nat)
        /\ L5.u8_at RSEGS M' 6759137 2
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 304) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 296) 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 288) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 280) (bv_unsigned (Z_to_bv 64 ((V 2%nat) - 256)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 264) 740144).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G19 G20 G21 G23 G24 G26 G27 K0 K1 K2 pvzI6 K4 K5 K6 pvzI7 pvzI8 pvzI9 K10 K11.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K7l; move K7l before pvzI7; pose proof (proj2 pvzI7) as K7r; move K7r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K8l; move K8l before pvzI8; pose proof (proj2 pvzI8) as K8r; move K8r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K9l; move K9l before pvzI9; pose proof (proj2 pvzI9) as K9r; move K9r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 38%nat => Z_to_bv 64 vz_38 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 38%nat => vz_38 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PadkYIa.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadkYIa.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadkYIa.kn0).
  { unfold know_ok, PadkYIa.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K11]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadkYIa.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadkYIa.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 320) <= bv_unsigned a < (vz_2 - 320) + 64) -> ~ ((0 + 6759137) <= bv_unsigned a < (0 + 6759137) + 1) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PadkYIa.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PadkYIa.ps0) with 0x6336c in Hms. change (SR.ps_regs PadkYIa.ps0) with (map (fun i => (i, nth i PadkYIa.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PadkYIa.ps0) with PadkYIa.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkYIa.regs0 PadkYIa.regs_out0 80 KS_adkYIa KS_adkYIa_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PadkYIa.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PadkYIa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYIa.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PadkYIa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYIa.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PadkYIa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYIa.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkYIa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYIa.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PadkYIa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYIa.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PadkYIa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYIa.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PadkYIa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYIa.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PadkYIa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear - HV38l HV38r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | f_equal; first [reflexivity | wordP' ZA Hag] | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadkYIb := LibSegBa_adkYIb_b.
Definition KS_adkYIb : list nat := Eval vm_compute in (BG.kept_list 80 PadkYIb.regs0 PadkYIb.regs_out0).
Lemma KS_adkYIb_ok : BG.kept_ok 80 PadkYIb.regs0 PadkYIb.regs_out0 KS_adkYIb = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkYIb_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 320) -> getr R (reg 8) = Z_to_bv 64 145632 -> getr R (reg 10) = Z_to_bv 64 8 -> getr R (reg 18) = Z_to_bv 64 6759112 -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5.writable RSEGS M ((V 2%nat) - 320) 64 ->
  L5KA.zeros_at M 2148295769 3 -> L5.writable RSEGS M 6759112 24 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((0 + 6759112) <= bv_unsigned a < (0 + 6759112) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((0 + 6759112) <= i < (0 + 6759112) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb2280 M) (st fx' R' 0x78370 M')
        /\ (forall x, In x KS_adkYIb -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 729908
        /\ getr R' (reg 9) = Z_to_bv 64 8
        /\ getr R' (reg 10) = Z_to_bv 64 6759113
        /\ getr R' (reg 11) = Z_to_bv 64 145632
        /\ getr R' (reg 12) = Z_to_bv 64 8
        /\ getr R' (reg 19) = Z_to_bv 64 6759113
        /\ L5.u8_at RSEGS M' 6759112 16).
Proof.
  intros pvzI1 G2 G8 G10 G18 G21 pvzI2 K1 K2 K3 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as K0l; move K0l before pvzI2; pose proof (proj2 pvzI2) as K0r; move K0r before pvzI2; clear pvzI2.
  set (vz_2 := V 2%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 3%nat. }
  assert (HR: regs_ok E PadkYIb.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadkYIb.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadkYIb.kn0).
  { unfold know_ok, PadkYIb.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K3]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadkYIb.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadkYIb.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((0 + 6759112) <= bv_unsigned a < (0 + 6759112) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PadkYIb.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PadkYIb.ps0) with 0x78370 in Hms. change (SR.ps_regs PadkYIb.ps0) with (map (fun i => (i, nth i PadkYIb.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PadkYIb.ps0) with PadkYIb.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkYIb.regs0 PadkYIb.regs_out0 80 KS_adkYIb KS_adkYIb_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PadkYIb.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PadkYIb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYIb.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PadkYIb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYIb.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkYIb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYIb.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PadkYIb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYIb.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PadkYIb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYIb.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PadkYIb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadkYIc := LibSegBa_adkYIc_b.
Definition KS_adkYIc : list nat := Eval vm_compute in (BG.kept_list 80 PadkYIc.regs0 PadkYIc.regs_out0).
Lemma KS_adkYIc_ok : BG.kept_ok 80 PadkYIc.regs0 PadkYIc.regs_out0 KS_adkYIc = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkYIc_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 18%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 320) -> getr R (reg 8) = Z_to_bv 64 145632 -> getr R (reg 9) = Z_to_bv 64 8 -> getr R (reg 18) = Z_to_bv 64 6759112 -> getr R (reg 19) = Z_to_bv 64 6759113 -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1249280 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5.writable RSEGS M ((V 2%nat) - 320) 64 -> L5KA.zeros_at M 2148295769 3 ->
  L5.writable RSEGS M 6759112 24 -> 4096 <= (V 50%nat) <= 140737488354816 -> 4096 <= (V 33%nat) <= 140737488355280 -> L5.u64_at RSEGS M ((V 2%nat) - 264) 740144 ->
  L5.u64_at RSEGS M ((V 2%nat) - 272) (V 2%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 280) ((V 2%nat) - 256) -> L5.u64_at RSEGS M ((V 2%nat) - 288) (V 18%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 296) 2147450880 ->
  L5.u64_at RSEGS M ((V 2%nat) - 304) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 312) (V 38%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((0 + 6759121) <= bv_unsigned a < (0 + 6759121) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((0 + 6759121) <= i < (0 + 6759121) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb2334 M) (st fx' R' 0x6da18 M')
        /\ (forall x, In x KS_adkYIc -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 740172
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 256)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 256)
        /\ getr R' (reg 10) = Z_to_bv 64 874172
        /\ getr R' (reg 11) = Z_to_bv 64 6759112
        /\ getr R' (reg 12) = Z_to_bv 64 1282768
        /\ getr R' (reg 18) = Z_to_bv 64 (V 18%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 2147450880
        /\ getr R' (reg 20) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 38%nat)
        /\ L5.u8_at RSEGS M' 6759121 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G18 G19 G21 K0 K1 K2 pvzI6 K4 K5 K6 K7 K8 pvzI7 pvzI8 K11 K12 K13 K14 K15 K16 K17.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV18l; move HV18l before pvzI2; pose proof (proj2 pvzI2) as HV18r; move HV18r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K9l; move K9l before pvzI7; pose proof (proj2 pvzI7) as K9r; move K9r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K10l; move K10l before pvzI8; pose proof (proj2 pvzI8) as K10r; move K10r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_18 := V 18%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 18%nat => Z_to_bv 64 vz_18 | 33%nat => Z_to_bv 64 vz_33 | 38%nat => Z_to_bv 64 vz_38 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 18%nat => vz_18 | 33%nat => vz_33 | 38%nat => vz_38 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PadkYIc.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadkYIc.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadkYIc.kn0).
  { unfold know_ok, PadkYIc.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV18l HV18r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV33l HV33r K10l K10r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K17]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadkYIc.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadkYIc.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((0 + 6759121) <= bv_unsigned a < (0 + 6759121) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PadkYIc.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PadkYIc.ps0) with 0x6da18 in Hms. change (SR.ps_regs PadkYIc.ps0) with (map (fun i => (i, nth i PadkYIc.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PadkYIc.ps0) with PadkYIc.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkYIc.regs0 PadkYIc.regs_out0 80 KS_adkYIc KS_adkYIc_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PadkYIc.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PadkYIc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYIc.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PadkYIc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYIc.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PadkYIc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYIc.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PadkYIc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYIc.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkYIc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYIc.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PadkYIc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYIc.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PadkYIc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYIc.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PadkYIc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYIc.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PadkYIc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYIc.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PadkYIc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYIc.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PadkYIc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadkYId := LibSegBa_adkYId_b.
Definition KS_adkYId : list nat := Eval vm_compute in (BG.kept_list 80 PadkYId.regs0 PadkYId.regs_out0).
Lemma KS_adkYId_ok : BG.kept_ok 80 PadkYId.regs0 PadkYId.regs_out0 KS_adkYId = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkYId_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (V 34%nat) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5.writable RSEGS M 6759136 2 ->
  4096 <= (V 50%nat) <= 140737488354816 -> 4096 <= (V 33%nat) <= 140737488355280 -> 4096 <= (V 34%nat) <= 140737488355312 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((0 + 6759136) <= bv_unsigned a < (0 + 6759136) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((0 + 6759136) <= i < (0 + 6759136) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb4b4c M) (st fx' R' 0xb3fbc M')
        /\ (forall x, In x KS_adkYId -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 740184
        /\ getr R' (reg 10) = Z_to_bv 64 6759136
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ L5.u8_at RSEGS M' 6759136 1
        /\ L5.u8_at RSEGS M' 6759137 1).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G19 G20 G21 G23 G24 G26 G27 pvzI6 K1 K2 K3 pvzI7 pvzI8 pvzI9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K4l; move K4l before pvzI7; pose proof (proj2 pvzI7) as K4r; move K4r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K5l; move K5l before pvzI8; pose proof (proj2 pvzI8) as K5r; move K5r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 38%nat => Z_to_bv 64 vz_38 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 38%nat => vz_38 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PadkYId.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadkYId.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadkYId.kn0).
  { unfold know_ok, PadkYId.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadkYId.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadkYId.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((0 + 6759136) <= bv_unsigned a < (0 + 6759136) + 2) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PadkYId.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PadkYId.ps0) with 0xb3fbc in Hms. change (SR.ps_regs PadkYId.ps0) with (map (fun i => (i, nth i PadkYId.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PadkYId.ps0) with PadkYId.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkYId.regs0 PadkYId.regs_out0 80 KS_adkYId KS_adkYId_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PadkYId.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PadkYId.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYId.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkYId.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYId.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PadkYId.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadkYNa := LibSegBa_adkYNa_b.
Definition KS_adkYNa : list nat := Eval vm_compute in (BG.kept_list 80 PadkYNa.regs0 PadkYNa.regs_out0).
Lemma KS_adkYNa_ok : BG.kept_ok 80 PadkYNa.regs0 PadkYNa.regs_out0 KS_adkYNa = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma adkYNa_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (V 34%nat) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 1249280 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5.writable RSEGS M ((V 2%nat) - 320) 64 -> 4096 <= (V 50%nat) <= 140737488354816 ->
  4096 <= (V 33%nat) <= 140737488355280 -> 4096 <= (V 34%nat) <= 140737488355312 -> L5.img_clear M 6759168 6759176 -> L5.writable RSEGS M 6759168 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 320) <= bv_unsigned a < ((V 2%nat) - 320) + 64) -> ~ ((0 + 6759169) <= bv_unsigned a < (0 + 6759169) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 320) <= i < ((V 2%nat) - 320) + 64) -> ~ ((0 + 6759169) <= i < (0 + 6759169) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3fbc M) (st fx' R' 0x6336c M')
        /\ (forall x, In x KS_adkYNa -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 729728
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 320)
        /\ getr R' (reg 8) = Z_to_bv 64 145664
        /\ getr R' (reg 10) = Z_to_bv 64 145664
        /\ getr R' (reg 11) = Z_to_bv 64 1309752
        /\ getr R' (reg 12) = Z_to_bv 64 2
        /\ getr R' (reg 18) = Z_to_bv 64 6759144
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 312) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 272) (V 2%nat)
        /\ L5.u8_at RSEGS M' 6759169 2
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 304) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 296) 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 288) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 280) (bv_unsigned (Z_to_bv 64 ((V 2%nat) - 256)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 264) 740228).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G19 G20 G21 G23 G24 G26 G27 K0 K1 K2 pvzI6 K4 K5 K6 pvzI7 pvzI8 pvzI9 K10 K11.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K7l; move K7l before pvzI7; pose proof (proj2 pvzI7) as K7r; move K7r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K8l; move K8l before pvzI8; pose proof (proj2 pvzI8) as K8r; move K8r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K9l; move K9l before pvzI9; pose proof (proj2 pvzI9) as K9r; move K9r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 38%nat => Z_to_bv 64 vz_38 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 38%nat => vz_38 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PadkYNa.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadkYNa.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadkYNa.kn0).
  { unfold know_ok, PadkYNa.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K11]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadkYNa.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadkYNa.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 320) <= bv_unsigned a < (vz_2 - 320) + 64) -> ~ ((0 + 6759169) <= bv_unsigned a < (0 + 6759169) + 1) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PadkYNa.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PadkYNa.ps0) with 0x6336c in Hms. change (SR.ps_regs PadkYNa.ps0) with (map (fun i => (i, nth i PadkYNa.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PadkYNa.ps0) with PadkYNa.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkYNa.regs0 PadkYNa.regs_out0 80 KS_adkYNa KS_adkYNa_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PadkYNa.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PadkYNa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYNa.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PadkYNa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYNa.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PadkYNa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYNa.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkYNa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYNa.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PadkYNa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYNa.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PadkYNa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYNa.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PadkYNa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYNa.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PadkYNa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear - HV38l HV38r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | f_equal; first [reflexivity | wordP' ZA Hag] | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadkYNb := LibSegBa_adkYNb_b.
Definition KS_adkYNb : list nat := Eval vm_compute in (BG.kept_list 80 PadkYNb.regs0 PadkYNb.regs_out0).
Lemma KS_adkYNb_ok : BG.kept_ok 80 PadkYNb.regs0 PadkYNb.regs_out0 KS_adkYNb = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkYNb_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 320) -> getr R (reg 8) = Z_to_bv 64 145664 -> getr R (reg 10) = Z_to_bv 64 3 -> getr R (reg 18) = Z_to_bv 64 6759144 -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5.writable RSEGS M ((V 2%nat) - 320) 64 ->
  L5KA.zeros_at M 2148295773 3 -> L5.writable RSEGS M 6759144 24 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((0 + 6759144) <= bv_unsigned a < (0 + 6759144) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((0 + 6759144) <= i < (0 + 6759144) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb2280 M) (st fx' R' 0x78370 M')
        /\ (forall x, In x KS_adkYNb -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 729908
        /\ getr R' (reg 9) = Z_to_bv 64 3
        /\ getr R' (reg 10) = Z_to_bv 64 6759145
        /\ getr R' (reg 11) = Z_to_bv 64 145664
        /\ getr R' (reg 12) = Z_to_bv 64 3
        /\ getr R' (reg 19) = Z_to_bv 64 6759145
        /\ L5.u8_at RSEGS M' 6759144 6).
Proof.
  intros pvzI1 G2 G8 G10 G18 G21 pvzI2 K1 K2 K3 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as K0l; move K0l before pvzI2; pose proof (proj2 pvzI2) as K0r; move K0r before pvzI2; clear pvzI2.
  set (vz_2 := V 2%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 3%nat. }
  assert (HR: regs_ok E PadkYNb.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadkYNb.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadkYNb.kn0).
  { unfold know_ok, PadkYNb.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K3]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadkYNb.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadkYNb.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((0 + 6759144) <= bv_unsigned a < (0 + 6759144) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PadkYNb.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PadkYNb.ps0) with 0x78370 in Hms. change (SR.ps_regs PadkYNb.ps0) with (map (fun i => (i, nth i PadkYNb.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PadkYNb.ps0) with PadkYNb.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkYNb.regs0 PadkYNb.regs_out0 80 KS_adkYNb KS_adkYNb_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PadkYNb.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PadkYNb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYNb.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PadkYNb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYNb.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkYNb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYNb.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PadkYNb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYNb.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PadkYNb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYNb.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PadkYNb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadkYNc := LibSegBa_adkYNc_b.
Definition KS_adkYNc : list nat := Eval vm_compute in (BG.kept_list 80 PadkYNc.regs0 PadkYNc.regs_out0).
Lemma KS_adkYNc_ok : BG.kept_ok 80 PadkYNc.regs0 PadkYNc.regs_out0 KS_adkYNc = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkYNc_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 18%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 320) -> getr R (reg 8) = Z_to_bv 64 145664 -> getr R (reg 9) = Z_to_bv 64 3 -> getr R (reg 18) = Z_to_bv 64 6759144 -> getr R (reg 19) = Z_to_bv 64 6759145 -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1249280 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5.writable RSEGS M ((V 2%nat) - 320) 64 -> L5KA.zeros_at M 2148295773 3 ->
  L5.writable RSEGS M 6759144 24 -> 4096 <= (V 50%nat) <= 140737488354816 -> 4096 <= (V 33%nat) <= 140737488355280 -> L5.u64_at RSEGS M ((V 2%nat) - 264) 740228 ->
  L5.u64_at RSEGS M ((V 2%nat) - 272) (V 2%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 280) ((V 2%nat) - 256) -> L5.u64_at RSEGS M ((V 2%nat) - 288) (V 18%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 296) 2147450880 ->
  L5.u64_at RSEGS M ((V 2%nat) - 304) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 312) (V 38%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((0 + 6759148) <= bv_unsigned a < (0 + 6759148) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((0 + 6759148) <= i < (0 + 6759148) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb2334 M) (st fx' R' 0x6da18 M')
        /\ (forall x, In x KS_adkYNc -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 740256
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 256)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 256)
        /\ getr R' (reg 10) = Z_to_bv 64 874172
        /\ getr R' (reg 11) = Z_to_bv 64 6759144
        /\ getr R' (reg 12) = Z_to_bv 64 1282768
        /\ getr R' (reg 18) = Z_to_bv 64 (V 18%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 2147450880
        /\ getr R' (reg 20) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 38%nat)
        /\ L5.u8_at RSEGS M' 6759148 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G18 G19 G21 K0 K1 K2 pvzI6 K4 K5 K6 K7 K8 pvzI7 pvzI8 K11 K12 K13 K14 K15 K16 K17.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV18l; move HV18l before pvzI2; pose proof (proj2 pvzI2) as HV18r; move HV18r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K9l; move K9l before pvzI7; pose proof (proj2 pvzI7) as K9r; move K9r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K10l; move K10l before pvzI8; pose proof (proj2 pvzI8) as K10r; move K10r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_18 := V 18%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 18%nat => Z_to_bv 64 vz_18 | 33%nat => Z_to_bv 64 vz_33 | 38%nat => Z_to_bv 64 vz_38 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 18%nat => vz_18 | 33%nat => vz_33 | 38%nat => vz_38 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PadkYNc.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadkYNc.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadkYNc.kn0).
  { unfold know_ok, PadkYNc.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV18l HV18r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV33l HV33r K10l K10r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K17]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadkYNc.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadkYNc.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((0 + 6759148) <= bv_unsigned a < (0 + 6759148) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PadkYNc.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PadkYNc.ps0) with 0x6da18 in Hms. change (SR.ps_regs PadkYNc.ps0) with (map (fun i => (i, nth i PadkYNc.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PadkYNc.ps0) with PadkYNc.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkYNc.regs0 PadkYNc.regs_out0 80 KS_adkYNc KS_adkYNc_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PadkYNc.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PadkYNc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYNc.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PadkYNc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYNc.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PadkYNc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYNc.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PadkYNc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYNc.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkYNc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYNc.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PadkYNc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYNc.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PadkYNc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYNc.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PadkYNc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYNc.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PadkYNc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYNc.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PadkYNc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYNc.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PadkYNc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadkYNd := LibSegBa_adkYNd_b.
Definition KS_adkYNd : list nat := Eval vm_compute in (BG.kept_list 80 PadkYNd.regs0 PadkYNd.regs_out0).
Lemma KS_adkYNd_ok : BG.kept_ok 80 PadkYNd.regs0 PadkYNd.regs_out0 KS_adkYNd = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkYNd_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (V 34%nat) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5.writable RSEGS M 6759168 2 ->
  4096 <= (V 50%nat) <= 140737488354816 -> 4096 <= (V 33%nat) <= 140737488355280 -> 4096 <= (V 34%nat) <= 140737488355312 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((0 + 6759168) <= bv_unsigned a < (0 + 6759168) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((0 + 6759168) <= i < (0 + 6759168) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb4ba0 M) (st fx' R' 0xb3fcc M')
        /\ (forall x, In x KS_adkYNd -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 740268
        /\ getr R' (reg 10) = Z_to_bv 64 6759168
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ L5.u8_at RSEGS M' 6759168 1
        /\ L5.u8_at RSEGS M' 6759169 1).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G19 G20 G21 G23 G24 G26 G27 pvzI6 K1 K2 K3 pvzI7 pvzI8 pvzI9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K4l; move K4l before pvzI7; pose proof (proj2 pvzI7) as K4r; move K4r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K5l; move K5l before pvzI8; pose proof (proj2 pvzI8) as K5r; move K5r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 38%nat => Z_to_bv 64 vz_38 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 38%nat => vz_38 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PadkYNd.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadkYNd.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadkYNd.kn0).
  { unfold know_ok, PadkYNd.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadkYNd.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadkYNd.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((0 + 6759168) <= bv_unsigned a < (0 + 6759168) + 2) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PadkYNd.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PadkYNd.ps0) with 0xb3fcc in Hms. change (SR.ps_regs PadkYNd.ps0) with (map (fun i => (i, nth i PadkYNd.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PadkYNd.ps0) with PadkYNd.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkYNd.regs0 PadkYNd.regs_out0 80 KS_adkYNd KS_adkYNd_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PadkYNd.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PadkYNd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYNd.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkYNd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkYNd.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PadkYNd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

End PNADP8.
