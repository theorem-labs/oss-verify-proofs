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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require LibSegBa_avlF5Z_b LibSegBa_avlF5P1_b LibSegBa_avlF5P2_b LibSegBa_avlF5P3_b LibSegBa_avlF5P4_b LibSegBa_avlF5P5_b LibSegBa_avlF5P6_b LibSegBa_avlF5P7_b LibSegBa_avlF6Z_b LibSegBa_avlF6P1_b LibSegBa_avlF6P2_b LibSegBa_avlF6P3_b LibSegBa_avlF6P4_b LibSegBa_avlF6P5_b LibSegBa_avlF6P6_b LibSegBa_avlF6P7_b LibSegBa_avlF7Z_b LibSegBa_avlF7P1_b LibSegBa_avlF7P2_b LibSegBa_avlF7P3_b LibSegBa_avlF7P4_b LibSegBa_avlF7P5_b LibSegBa_avlF7P6_b LibSegBa_avlF7P7_b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PMAVALP3.
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
Module PavlF5Z := LibSegBa_avlF5Z_b.
Definition KS_avlF5Z_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF5Z.regs0 PavlF5Z.regs_out0).
Lemma KS_avlF5Z_0_ok : BG.kept_ok 60 PavlF5Z.regs0 PavlF5Z.regs_out0 KS_avlF5Z_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF5Z_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF5Z.regs0 PavlF5Z.regs_out1).
Lemma KS_avlF5Z_1_ok : BG.kept_ok 60 PavlF5Z.regs0 PavlF5Z.regs_out1 KS_avlF5Z_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlF5Z_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 18446744073709551615 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 145280 -> getr R (reg 19) = Z_to_bv 64 18446744073709406335 -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 5) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5KA.zeros_at M ((((V 33%nat) + 5) / 8) + 2147450880) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb30ac M) (st fx' R' 0xb312c M')
        /\ (forall x, In x KS_avlF5Z_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ getr R' (reg 11) = Z_to_bv 64 0)
      \/ (msteps RSEGS (st fx R 0xb30ac M) (st fx' R' 0xb30cc M')
        /\ (forall x, In x KS_avlF5Z_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 5))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavlF5Z.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlF5Z.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlF5Z.kn0).
  { unfold know_ok, PavlF5Z.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlF5Z.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlF5Z.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavlF5Z.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavlF5Z.ps0) with 0xb312c in Hms. change (SR.ps_regs PavlF5Z.ps0) with (map (fun i => (i, nth i PavlF5Z.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF5Z.ps0) with PavlF5Z.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF5Z.regs0 PavlF5Z.regs_out0 60 KS_avlF5Z_0 KS_avlF5Z_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF5Z.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavlF5Z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PavlF5Z.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF5Z.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
  - right.
    change (SR.ps_pc PavlF5Z.ps1) with 0xb30cc in Hms. change (SR.ps_regs PavlF5Z.ps1) with (map (fun i => (i, nth i PavlF5Z.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF5Z.ps1) with PavlF5Z.cells1 in Hcells. unfold PavlF5Z.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF5Z.regs0 PavlF5Z.regs_out1 60 KS_avlF5Z_1 KS_avlF5Z_1_ok HR Hag Hregs j Hj). }
    rewrite (BG.out_reg PavlF5Z.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF5Z.regs_out1]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavlF5P1 := LibSegBa_avlF5P1_b.
Definition KS_avlF5P1_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF5P1.regs0 PavlF5P1.regs_out0).
Lemma KS_avlF5P1_0_ok : BG.kept_ok 60 PavlF5P1.regs0 PavlF5P1.regs_out0 KS_avlF5P1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF5P1_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF5P1.regs0 PavlF5P1.regs_out1).
Lemma KS_avlF5P1_1_ok : BG.kept_ok 60 PavlF5P1.regs0 PavlF5P1.regs_out1 KS_avlF5P1_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlF5P1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 18446744073709551615 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 145280 -> getr R (reg 19) = Z_to_bv 64 18446744073709406335 -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 5) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 5) / 8) + 2147450880) 1 -> 0 <= (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7) <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb30ac M) (st fx' R' 0xb312c M')
        /\ (forall x, In x KS_avlF5P1_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 25) = Z_to_bv 64 0)
      \/ (msteps RSEGS (st fx R 0xb30ac M) (st fx' R' 0xb30cc M')
        /\ (forall x, In x KS_avlF5P1_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ getr R' (reg 25) = Z_to_bv 64 0)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavlF5P1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlF5P1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlF5P1.kn0).
  { unfold know_ok, PavlF5P1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlF5P1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlF5P1.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavlF5P1.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavlF5P1.ps0) with 0xb312c in Hms. change (SR.ps_regs PavlF5P1.ps0) with (map (fun i => (i, nth i PavlF5P1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF5P1.ps0) with PavlF5P1.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF5P1.regs0 PavlF5P1.regs_out0 60 KS_avlF5P1_0 KS_avlF5P1_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF5P1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavlF5P1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF5P1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF5P1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF5P1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavlF5P1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PavlF5P1.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PavlF5P1.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
  - right.
    change (SR.ps_pc PavlF5P1.ps1) with 0xb30cc in Hms. change (SR.ps_regs PavlF5P1.ps1) with (map (fun i => (i, nth i PavlF5P1.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF5P1.ps1) with PavlF5P1.cells1 in Hcells. unfold PavlF5P1.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF5P1.regs0 PavlF5P1.regs_out1 60 KS_avlF5P1_1 KS_avlF5P1_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF5P1.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF5P1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PavlF5P1.regs_out1 E' R' 25 Hregs) by (clear; lia). cbn [nth PavlF5P1.regs_out1]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavlF5P2 := LibSegBa_avlF5P2_b.
Definition KS_avlF5P2_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF5P2.regs0 PavlF5P2.regs_out0).
Lemma KS_avlF5P2_0_ok : BG.kept_ok 60 PavlF5P2.regs0 PavlF5P2.regs_out0 KS_avlF5P2_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF5P2_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF5P2.regs0 PavlF5P2.regs_out1).
Lemma KS_avlF5P2_1_ok : BG.kept_ok 60 PavlF5P2.regs0 PavlF5P2.regs_out1 KS_avlF5P2_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlF5P2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 18446744073709551615 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 145280 -> getr R (reg 19) = Z_to_bv 64 18446744073709406335 -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 5) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 5) / 8) + 2147450880) 2 -> 0 <= (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb30ac M) (st fx' R' 0xb312c M')
        /\ (forall x, In x KS_avlF5P2_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ bv_unsigned (getr R' (reg 12)) = (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7))
      \/ (msteps RSEGS (st fx R 0xb30ac M) (st fx' R' 0xb30cc M')
        /\ (forall x, In x KS_avlF5P2_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavlF5P2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlF5P2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlF5P2.kn0).
  { unfold know_ok, PavlF5P2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlF5P2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlF5P2.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavlF5P2.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavlF5P2.ps0) with 0xb312c in Hms. change (SR.ps_regs PavlF5P2.ps0) with (map (fun i => (i, nth i PavlF5P2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF5P2.ps0) with PavlF5P2.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF5P2.regs0 PavlF5P2.regs_out0 60 KS_avlF5P2_0 KS_avlF5P2_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF5P2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavlF5P2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF5P2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF5P2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF5P2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavlF5P2.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    rewrite (BG.out_reg PavlF5P2.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PavlF5P2.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. 
  - right.
    change (SR.ps_pc PavlF5P2.ps1) with 0xb30cc in Hms. change (SR.ps_regs PavlF5P2.ps1) with (map (fun i => (i, nth i PavlF5P2.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF5P2.ps1) with PavlF5P2.cells1 in Hcells. unfold PavlF5P2.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF5P2.regs0 PavlF5P2.regs_out1 60 KS_avlF5P2_1 KS_avlF5P2_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF5P2.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF5P2.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PavlF5P2.regs_out1 E' R' 25 Hregs) by (clear; lia). cbn [nth PavlF5P2.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavlF5P3 := LibSegBa_avlF5P3_b.
Definition KS_avlF5P3_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF5P3.regs0 PavlF5P3.regs_out0).
Lemma KS_avlF5P3_0_ok : BG.kept_ok 60 PavlF5P3.regs0 PavlF5P3.regs_out0 KS_avlF5P3_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF5P3_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF5P3.regs0 PavlF5P3.regs_out1).
Lemma KS_avlF5P3_1_ok : BG.kept_ok 60 PavlF5P3.regs0 PavlF5P3.regs_out1 KS_avlF5P3_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlF5P3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 18446744073709551615 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 145280 -> getr R (reg 19) = Z_to_bv 64 18446744073709406335 -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 5) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 5) / 8) + 2147450880) 3 -> 0 <= (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7) <= 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb30ac M) (st fx' R' 0xb312c M')
        /\ (forall x, In x KS_avlF5P3_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ getr R' (reg 11) = Z_to_bv 64 3
        /\ bv_unsigned (getr R' (reg 12)) = (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7))
      \/ (msteps RSEGS (st fx R 0xb30ac M) (st fx' R' 0xb30cc M')
        /\ (forall x, In x KS_avlF5P3_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavlF5P3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlF5P3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlF5P3.kn0).
  { unfold know_ok, PavlF5P3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlF5P3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlF5P3.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavlF5P3.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavlF5P3.ps0) with 0xb312c in Hms. change (SR.ps_regs PavlF5P3.ps0) with (map (fun i => (i, nth i PavlF5P3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF5P3.ps0) with PavlF5P3.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF5P3.regs0 PavlF5P3.regs_out0 60 KS_avlF5P3_0 KS_avlF5P3_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF5P3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavlF5P3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF5P3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF5P3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF5P3.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavlF5P3.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    rewrite (BG.out_reg PavlF5P3.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PavlF5P3.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. 
  - right.
    change (SR.ps_pc PavlF5P3.ps1) with 0xb30cc in Hms. change (SR.ps_regs PavlF5P3.ps1) with (map (fun i => (i, nth i PavlF5P3.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF5P3.ps1) with PavlF5P3.cells1 in Hcells. unfold PavlF5P3.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF5P3.regs0 PavlF5P3.regs_out1 60 KS_avlF5P3_1 KS_avlF5P3_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF5P3.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF5P3.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PavlF5P3.regs_out1 E' R' 25 Hregs) by (clear; lia). cbn [nth PavlF5P3.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavlF5P4 := LibSegBa_avlF5P4_b.
Definition KS_avlF5P4_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF5P4.regs0 PavlF5P4.regs_out0).
Lemma KS_avlF5P4_0_ok : BG.kept_ok 60 PavlF5P4.regs0 PavlF5P4.regs_out0 KS_avlF5P4_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF5P4_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF5P4.regs0 PavlF5P4.regs_out1).
Lemma KS_avlF5P4_1_ok : BG.kept_ok 60 PavlF5P4.regs0 PavlF5P4.regs_out1 KS_avlF5P4_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlF5P4_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 18446744073709551615 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 145280 -> getr R (reg 19) = Z_to_bv 64 18446744073709406335 -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 5) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 5) / 8) + 2147450880) 4 -> 0 <= (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7) <= 3 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb30ac M) (st fx' R' 0xb312c M')
        /\ (forall x, In x KS_avlF5P4_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ getr R' (reg 11) = Z_to_bv 64 4
        /\ bv_unsigned (getr R' (reg 12)) = (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7))
      \/ (msteps RSEGS (st fx R 0xb30ac M) (st fx' R' 0xb30cc M')
        /\ (forall x, In x KS_avlF5P4_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavlF5P4.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlF5P4.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlF5P4.kn0).
  { unfold know_ok, PavlF5P4.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlF5P4.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlF5P4.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavlF5P4.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavlF5P4.ps0) with 0xb312c in Hms. change (SR.ps_regs PavlF5P4.ps0) with (map (fun i => (i, nth i PavlF5P4.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF5P4.ps0) with PavlF5P4.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF5P4.regs0 PavlF5P4.regs_out0 60 KS_avlF5P4_0 KS_avlF5P4_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF5P4.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavlF5P4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF5P4.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF5P4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF5P4.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavlF5P4.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    rewrite (BG.out_reg PavlF5P4.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PavlF5P4.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. 
  - right.
    change (SR.ps_pc PavlF5P4.ps1) with 0xb30cc in Hms. change (SR.ps_regs PavlF5P4.ps1) with (map (fun i => (i, nth i PavlF5P4.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF5P4.ps1) with PavlF5P4.cells1 in Hcells. unfold PavlF5P4.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF5P4.regs0 PavlF5P4.regs_out1 60 KS_avlF5P4_1 KS_avlF5P4_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF5P4.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF5P4.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PavlF5P4.regs_out1 E' R' 25 Hregs) by (clear; lia). cbn [nth PavlF5P4.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavlF5P5 := LibSegBa_avlF5P5_b.
Definition KS_avlF5P5_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF5P5.regs0 PavlF5P5.regs_out0).
Lemma KS_avlF5P5_0_ok : BG.kept_ok 60 PavlF5P5.regs0 PavlF5P5.regs_out0 KS_avlF5P5_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF5P5_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF5P5.regs0 PavlF5P5.regs_out1).
Lemma KS_avlF5P5_1_ok : BG.kept_ok 60 PavlF5P5.regs0 PavlF5P5.regs_out1 KS_avlF5P5_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlF5P5_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 18446744073709551615 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 145280 -> getr R (reg 19) = Z_to_bv 64 18446744073709406335 -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 5) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 5) / 8) + 2147450880) 5 -> 0 <= (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7) <= 4 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb30ac M) (st fx' R' 0xb312c M')
        /\ (forall x, In x KS_avlF5P5_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ getr R' (reg 11) = Z_to_bv 64 5
        /\ bv_unsigned (getr R' (reg 12)) = (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7))
      \/ (msteps RSEGS (st fx R 0xb30ac M) (st fx' R' 0xb30cc M')
        /\ (forall x, In x KS_avlF5P5_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavlF5P5.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlF5P5.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlF5P5.kn0).
  { unfold know_ok, PavlF5P5.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlF5P5.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlF5P5.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavlF5P5.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavlF5P5.ps0) with 0xb312c in Hms. change (SR.ps_regs PavlF5P5.ps0) with (map (fun i => (i, nth i PavlF5P5.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF5P5.ps0) with PavlF5P5.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF5P5.regs0 PavlF5P5.regs_out0 60 KS_avlF5P5_0 KS_avlF5P5_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF5P5.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavlF5P5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF5P5.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF5P5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF5P5.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavlF5P5.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    rewrite (BG.out_reg PavlF5P5.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PavlF5P5.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. 
  - right.
    change (SR.ps_pc PavlF5P5.ps1) with 0xb30cc in Hms. change (SR.ps_regs PavlF5P5.ps1) with (map (fun i => (i, nth i PavlF5P5.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF5P5.ps1) with PavlF5P5.cells1 in Hcells. unfold PavlF5P5.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF5P5.regs0 PavlF5P5.regs_out1 60 KS_avlF5P5_1 KS_avlF5P5_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF5P5.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF5P5.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PavlF5P5.regs_out1 E' R' 25 Hregs) by (clear; lia). cbn [nth PavlF5P5.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavlF5P6 := LibSegBa_avlF5P6_b.
Definition KS_avlF5P6_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF5P6.regs0 PavlF5P6.regs_out0).
Lemma KS_avlF5P6_0_ok : BG.kept_ok 60 PavlF5P6.regs0 PavlF5P6.regs_out0 KS_avlF5P6_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF5P6_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF5P6.regs0 PavlF5P6.regs_out1).
Lemma KS_avlF5P6_1_ok : BG.kept_ok 60 PavlF5P6.regs0 PavlF5P6.regs_out1 KS_avlF5P6_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlF5P6_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 18446744073709551615 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 145280 -> getr R (reg 19) = Z_to_bv 64 18446744073709406335 -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 5) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 5) / 8) + 2147450880) 6 -> 0 <= (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7) <= 5 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb30ac M) (st fx' R' 0xb312c M')
        /\ (forall x, In x KS_avlF5P6_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ bv_unsigned (getr R' (reg 12)) = (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7))
      \/ (msteps RSEGS (st fx R 0xb30ac M) (st fx' R' 0xb30cc M')
        /\ (forall x, In x KS_avlF5P6_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavlF5P6.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlF5P6.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlF5P6.kn0).
  { unfold know_ok, PavlF5P6.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlF5P6.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlF5P6.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavlF5P6.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavlF5P6.ps0) with 0xb312c in Hms. change (SR.ps_regs PavlF5P6.ps0) with (map (fun i => (i, nth i PavlF5P6.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF5P6.ps0) with PavlF5P6.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF5P6.regs0 PavlF5P6.regs_out0 60 KS_avlF5P6_0 KS_avlF5P6_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF5P6.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavlF5P6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF5P6.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF5P6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF5P6.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavlF5P6.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    rewrite (BG.out_reg PavlF5P6.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PavlF5P6.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. 
  - right.
    change (SR.ps_pc PavlF5P6.ps1) with 0xb30cc in Hms. change (SR.ps_regs PavlF5P6.ps1) with (map (fun i => (i, nth i PavlF5P6.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF5P6.ps1) with PavlF5P6.cells1 in Hcells. unfold PavlF5P6.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF5P6.regs0 PavlF5P6.regs_out1 60 KS_avlF5P6_1 KS_avlF5P6_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF5P6.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF5P6.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PavlF5P6.regs_out1 E' R' 25 Hregs) by (clear; lia). cbn [nth PavlF5P6.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavlF5P7 := LibSegBa_avlF5P7_b.
Definition KS_avlF5P7_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF5P7.regs0 PavlF5P7.regs_out0).
Lemma KS_avlF5P7_0_ok : BG.kept_ok 60 PavlF5P7.regs0 PavlF5P7.regs_out0 KS_avlF5P7_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF5P7_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF5P7.regs0 PavlF5P7.regs_out1).
Lemma KS_avlF5P7_1_ok : BG.kept_ok 60 PavlF5P7.regs0 PavlF5P7.regs_out1 KS_avlF5P7_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlF5P7_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 18446744073709551615 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 145280 -> getr R (reg 19) = Z_to_bv 64 18446744073709406335 -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 5) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 5) / 8) + 2147450880) 7 -> 0 <= (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7) <= 6 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb30ac M) (st fx' R' 0xb312c M')
        /\ (forall x, In x KS_avlF5P7_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ getr R' (reg 11) = Z_to_bv 64 7
        /\ bv_unsigned (getr R' (reg 12)) = (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7))
      \/ (msteps RSEGS (st fx R 0xb30ac M) (st fx' R' 0xb30cc M')
        /\ (forall x, In x KS_avlF5P7_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavlF5P7.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlF5P7.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlF5P7.kn0).
  { unfold know_ok, PavlF5P7.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlF5P7.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlF5P7.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavlF5P7.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavlF5P7.ps0) with 0xb312c in Hms. change (SR.ps_regs PavlF5P7.ps0) with (map (fun i => (i, nth i PavlF5P7.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF5P7.ps0) with PavlF5P7.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF5P7.regs0 PavlF5P7.regs_out0 60 KS_avlF5P7_0 KS_avlF5P7_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF5P7.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavlF5P7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF5P7.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF5P7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF5P7.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavlF5P7.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    rewrite (BG.out_reg PavlF5P7.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PavlF5P7.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. 
  - right.
    change (SR.ps_pc PavlF5P7.ps1) with 0xb30cc in Hms. change (SR.ps_regs PavlF5P7.ps1) with (map (fun i => (i, nth i PavlF5P7.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF5P7.ps1) with PavlF5P7.cells1 in Hcells. unfold PavlF5P7.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF5P7.regs0 PavlF5P7.regs_out1 60 KS_avlF5P7_1 KS_avlF5P7_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF5P7.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF5P7.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PavlF5P7.regs_out1 E' R' 25 Hregs) by (clear; lia). cbn [nth PavlF5P7.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavlF6Z := LibSegBa_avlF6Z_b.
Definition KS_avlF6Z_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF6Z.regs0 PavlF6Z.regs_out0).
Lemma KS_avlF6Z_0_ok : BG.kept_ok 60 PavlF6Z.regs0 PavlF6Z.regs_out0 KS_avlF6Z_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF6Z_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF6Z.regs0 PavlF6Z.regs_out1).
Lemma KS_avlF6Z_1_ok : BG.kept_ok 60 PavlF6Z.regs0 PavlF6Z.regs_out1 KS_avlF6Z_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlF6Z_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 18446744073709551615 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 145280 -> getr R (reg 19) = Z_to_bv 64 18446744073709406335 -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 6) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5KA.zeros_at M ((((V 33%nat) + 6) / 8) + 2147450880) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb30cc M) (st fx' R' 0xb312c M')
        /\ (forall x, In x KS_avlF6Z_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ getr R' (reg 11) = Z_to_bv 64 0)
      \/ (msteps RSEGS (st fx R 0xb30cc M) (st fx' R' 0xb30ec M')
        /\ (forall x, In x KS_avlF6Z_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 6))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavlF6Z.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlF6Z.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlF6Z.kn0).
  { unfold know_ok, PavlF6Z.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlF6Z.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlF6Z.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavlF6Z.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavlF6Z.ps0) with 0xb312c in Hms. change (SR.ps_regs PavlF6Z.ps0) with (map (fun i => (i, nth i PavlF6Z.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF6Z.ps0) with PavlF6Z.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF6Z.regs0 PavlF6Z.regs_out0 60 KS_avlF6Z_0 KS_avlF6Z_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF6Z.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavlF6Z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PavlF6Z.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF6Z.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
  - right.
    change (SR.ps_pc PavlF6Z.ps1) with 0xb30ec in Hms. change (SR.ps_regs PavlF6Z.ps1) with (map (fun i => (i, nth i PavlF6Z.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF6Z.ps1) with PavlF6Z.cells1 in Hcells. unfold PavlF6Z.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF6Z.regs0 PavlF6Z.regs_out1 60 KS_avlF6Z_1 KS_avlF6Z_1_ok HR Hag Hregs j Hj). }
    rewrite (BG.out_reg PavlF6Z.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF6Z.regs_out1]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavlF6P1 := LibSegBa_avlF6P1_b.
Definition KS_avlF6P1_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF6P1.regs0 PavlF6P1.regs_out0).
Lemma KS_avlF6P1_0_ok : BG.kept_ok 60 PavlF6P1.regs0 PavlF6P1.regs_out0 KS_avlF6P1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF6P1_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF6P1.regs0 PavlF6P1.regs_out1).
Lemma KS_avlF6P1_1_ok : BG.kept_ok 60 PavlF6P1.regs0 PavlF6P1.regs_out1 KS_avlF6P1_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlF6P1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 18446744073709551615 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 145280 -> getr R (reg 19) = Z_to_bv 64 18446744073709406335 -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 6) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 6) / 8) + 2147450880) 1 -> 0 <= (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7) <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb30cc M) (st fx' R' 0xb312c M')
        /\ (forall x, In x KS_avlF6P1_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 25) = Z_to_bv 64 0)
      \/ (msteps RSEGS (st fx R 0xb30cc M) (st fx' R' 0xb30ec M')
        /\ (forall x, In x KS_avlF6P1_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ getr R' (reg 25) = Z_to_bv 64 0)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavlF6P1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlF6P1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlF6P1.kn0).
  { unfold know_ok, PavlF6P1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlF6P1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlF6P1.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavlF6P1.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavlF6P1.ps0) with 0xb312c in Hms. change (SR.ps_regs PavlF6P1.ps0) with (map (fun i => (i, nth i PavlF6P1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF6P1.ps0) with PavlF6P1.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF6P1.regs0 PavlF6P1.regs_out0 60 KS_avlF6P1_0 KS_avlF6P1_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF6P1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavlF6P1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF6P1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF6P1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF6P1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavlF6P1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PavlF6P1.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PavlF6P1.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
  - right.
    change (SR.ps_pc PavlF6P1.ps1) with 0xb30ec in Hms. change (SR.ps_regs PavlF6P1.ps1) with (map (fun i => (i, nth i PavlF6P1.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF6P1.ps1) with PavlF6P1.cells1 in Hcells. unfold PavlF6P1.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF6P1.regs0 PavlF6P1.regs_out1 60 KS_avlF6P1_1 KS_avlF6P1_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF6P1.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF6P1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PavlF6P1.regs_out1 E' R' 25 Hregs) by (clear; lia). cbn [nth PavlF6P1.regs_out1]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavlF6P2 := LibSegBa_avlF6P2_b.
Definition KS_avlF6P2_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF6P2.regs0 PavlF6P2.regs_out0).
Lemma KS_avlF6P2_0_ok : BG.kept_ok 60 PavlF6P2.regs0 PavlF6P2.regs_out0 KS_avlF6P2_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF6P2_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF6P2.regs0 PavlF6P2.regs_out1).
Lemma KS_avlF6P2_1_ok : BG.kept_ok 60 PavlF6P2.regs0 PavlF6P2.regs_out1 KS_avlF6P2_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlF6P2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 18446744073709551615 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 145280 -> getr R (reg 19) = Z_to_bv 64 18446744073709406335 -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 6) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 6) / 8) + 2147450880) 2 -> 0 <= (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb30cc M) (st fx' R' 0xb312c M')
        /\ (forall x, In x KS_avlF6P2_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ bv_unsigned (getr R' (reg 12)) = (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7))
      \/ (msteps RSEGS (st fx R 0xb30cc M) (st fx' R' 0xb30ec M')
        /\ (forall x, In x KS_avlF6P2_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavlF6P2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlF6P2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlF6P2.kn0).
  { unfold know_ok, PavlF6P2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlF6P2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlF6P2.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavlF6P2.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavlF6P2.ps0) with 0xb312c in Hms. change (SR.ps_regs PavlF6P2.ps0) with (map (fun i => (i, nth i PavlF6P2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF6P2.ps0) with PavlF6P2.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF6P2.regs0 PavlF6P2.regs_out0 60 KS_avlF6P2_0 KS_avlF6P2_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF6P2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavlF6P2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF6P2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF6P2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF6P2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavlF6P2.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    rewrite (BG.out_reg PavlF6P2.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PavlF6P2.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. 
  - right.
    change (SR.ps_pc PavlF6P2.ps1) with 0xb30ec in Hms. change (SR.ps_regs PavlF6P2.ps1) with (map (fun i => (i, nth i PavlF6P2.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF6P2.ps1) with PavlF6P2.cells1 in Hcells. unfold PavlF6P2.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF6P2.regs0 PavlF6P2.regs_out1 60 KS_avlF6P2_1 KS_avlF6P2_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF6P2.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF6P2.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PavlF6P2.regs_out1 E' R' 25 Hregs) by (clear; lia). cbn [nth PavlF6P2.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavlF6P3 := LibSegBa_avlF6P3_b.
Definition KS_avlF6P3_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF6P3.regs0 PavlF6P3.regs_out0).
Lemma KS_avlF6P3_0_ok : BG.kept_ok 60 PavlF6P3.regs0 PavlF6P3.regs_out0 KS_avlF6P3_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF6P3_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF6P3.regs0 PavlF6P3.regs_out1).
Lemma KS_avlF6P3_1_ok : BG.kept_ok 60 PavlF6P3.regs0 PavlF6P3.regs_out1 KS_avlF6P3_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlF6P3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 18446744073709551615 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 145280 -> getr R (reg 19) = Z_to_bv 64 18446744073709406335 -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 6) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 6) / 8) + 2147450880) 3 -> 0 <= (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7) <= 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb30cc M) (st fx' R' 0xb312c M')
        /\ (forall x, In x KS_avlF6P3_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ getr R' (reg 11) = Z_to_bv 64 3
        /\ bv_unsigned (getr R' (reg 12)) = (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7))
      \/ (msteps RSEGS (st fx R 0xb30cc M) (st fx' R' 0xb30ec M')
        /\ (forall x, In x KS_avlF6P3_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavlF6P3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlF6P3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlF6P3.kn0).
  { unfold know_ok, PavlF6P3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlF6P3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlF6P3.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavlF6P3.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavlF6P3.ps0) with 0xb312c in Hms. change (SR.ps_regs PavlF6P3.ps0) with (map (fun i => (i, nth i PavlF6P3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF6P3.ps0) with PavlF6P3.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF6P3.regs0 PavlF6P3.regs_out0 60 KS_avlF6P3_0 KS_avlF6P3_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF6P3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavlF6P3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF6P3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF6P3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF6P3.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavlF6P3.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    rewrite (BG.out_reg PavlF6P3.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PavlF6P3.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. 
  - right.
    change (SR.ps_pc PavlF6P3.ps1) with 0xb30ec in Hms. change (SR.ps_regs PavlF6P3.ps1) with (map (fun i => (i, nth i PavlF6P3.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF6P3.ps1) with PavlF6P3.cells1 in Hcells. unfold PavlF6P3.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF6P3.regs0 PavlF6P3.regs_out1 60 KS_avlF6P3_1 KS_avlF6P3_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF6P3.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF6P3.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PavlF6P3.regs_out1 E' R' 25 Hregs) by (clear; lia). cbn [nth PavlF6P3.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavlF6P4 := LibSegBa_avlF6P4_b.
Definition KS_avlF6P4_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF6P4.regs0 PavlF6P4.regs_out0).
Lemma KS_avlF6P4_0_ok : BG.kept_ok 60 PavlF6P4.regs0 PavlF6P4.regs_out0 KS_avlF6P4_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF6P4_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF6P4.regs0 PavlF6P4.regs_out1).
Lemma KS_avlF6P4_1_ok : BG.kept_ok 60 PavlF6P4.regs0 PavlF6P4.regs_out1 KS_avlF6P4_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlF6P4_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 18446744073709551615 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 145280 -> getr R (reg 19) = Z_to_bv 64 18446744073709406335 -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 6) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 6) / 8) + 2147450880) 4 -> 0 <= (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7) <= 3 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb30cc M) (st fx' R' 0xb312c M')
        /\ (forall x, In x KS_avlF6P4_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ getr R' (reg 11) = Z_to_bv 64 4
        /\ bv_unsigned (getr R' (reg 12)) = (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7))
      \/ (msteps RSEGS (st fx R 0xb30cc M) (st fx' R' 0xb30ec M')
        /\ (forall x, In x KS_avlF6P4_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavlF6P4.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlF6P4.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlF6P4.kn0).
  { unfold know_ok, PavlF6P4.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlF6P4.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlF6P4.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavlF6P4.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavlF6P4.ps0) with 0xb312c in Hms. change (SR.ps_regs PavlF6P4.ps0) with (map (fun i => (i, nth i PavlF6P4.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF6P4.ps0) with PavlF6P4.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF6P4.regs0 PavlF6P4.regs_out0 60 KS_avlF6P4_0 KS_avlF6P4_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF6P4.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavlF6P4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF6P4.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF6P4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF6P4.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavlF6P4.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    rewrite (BG.out_reg PavlF6P4.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PavlF6P4.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. 
  - right.
    change (SR.ps_pc PavlF6P4.ps1) with 0xb30ec in Hms. change (SR.ps_regs PavlF6P4.ps1) with (map (fun i => (i, nth i PavlF6P4.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF6P4.ps1) with PavlF6P4.cells1 in Hcells. unfold PavlF6P4.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF6P4.regs0 PavlF6P4.regs_out1 60 KS_avlF6P4_1 KS_avlF6P4_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF6P4.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF6P4.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PavlF6P4.regs_out1 E' R' 25 Hregs) by (clear; lia). cbn [nth PavlF6P4.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavlF6P5 := LibSegBa_avlF6P5_b.
Definition KS_avlF6P5_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF6P5.regs0 PavlF6P5.regs_out0).
Lemma KS_avlF6P5_0_ok : BG.kept_ok 60 PavlF6P5.regs0 PavlF6P5.regs_out0 KS_avlF6P5_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF6P5_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF6P5.regs0 PavlF6P5.regs_out1).
Lemma KS_avlF6P5_1_ok : BG.kept_ok 60 PavlF6P5.regs0 PavlF6P5.regs_out1 KS_avlF6P5_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlF6P5_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 18446744073709551615 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 145280 -> getr R (reg 19) = Z_to_bv 64 18446744073709406335 -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 6) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 6) / 8) + 2147450880) 5 -> 0 <= (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7) <= 4 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb30cc M) (st fx' R' 0xb312c M')
        /\ (forall x, In x KS_avlF6P5_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ getr R' (reg 11) = Z_to_bv 64 5
        /\ bv_unsigned (getr R' (reg 12)) = (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7))
      \/ (msteps RSEGS (st fx R 0xb30cc M) (st fx' R' 0xb30ec M')
        /\ (forall x, In x KS_avlF6P5_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavlF6P5.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlF6P5.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlF6P5.kn0).
  { unfold know_ok, PavlF6P5.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlF6P5.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlF6P5.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavlF6P5.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavlF6P5.ps0) with 0xb312c in Hms. change (SR.ps_regs PavlF6P5.ps0) with (map (fun i => (i, nth i PavlF6P5.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF6P5.ps0) with PavlF6P5.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF6P5.regs0 PavlF6P5.regs_out0 60 KS_avlF6P5_0 KS_avlF6P5_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF6P5.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavlF6P5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF6P5.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF6P5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF6P5.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavlF6P5.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    rewrite (BG.out_reg PavlF6P5.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PavlF6P5.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. 
  - right.
    change (SR.ps_pc PavlF6P5.ps1) with 0xb30ec in Hms. change (SR.ps_regs PavlF6P5.ps1) with (map (fun i => (i, nth i PavlF6P5.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF6P5.ps1) with PavlF6P5.cells1 in Hcells. unfold PavlF6P5.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF6P5.regs0 PavlF6P5.regs_out1 60 KS_avlF6P5_1 KS_avlF6P5_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF6P5.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF6P5.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PavlF6P5.regs_out1 E' R' 25 Hregs) by (clear; lia). cbn [nth PavlF6P5.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavlF6P6 := LibSegBa_avlF6P6_b.
Definition KS_avlF6P6_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF6P6.regs0 PavlF6P6.regs_out0).
Lemma KS_avlF6P6_0_ok : BG.kept_ok 60 PavlF6P6.regs0 PavlF6P6.regs_out0 KS_avlF6P6_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF6P6_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF6P6.regs0 PavlF6P6.regs_out1).
Lemma KS_avlF6P6_1_ok : BG.kept_ok 60 PavlF6P6.regs0 PavlF6P6.regs_out1 KS_avlF6P6_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlF6P6_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 18446744073709551615 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 145280 -> getr R (reg 19) = Z_to_bv 64 18446744073709406335 -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 6) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 6) / 8) + 2147450880) 6 -> 0 <= (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7) <= 5 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb30cc M) (st fx' R' 0xb312c M')
        /\ (forall x, In x KS_avlF6P6_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ bv_unsigned (getr R' (reg 12)) = (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7))
      \/ (msteps RSEGS (st fx R 0xb30cc M) (st fx' R' 0xb30ec M')
        /\ (forall x, In x KS_avlF6P6_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavlF6P6.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlF6P6.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlF6P6.kn0).
  { unfold know_ok, PavlF6P6.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlF6P6.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlF6P6.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavlF6P6.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavlF6P6.ps0) with 0xb312c in Hms. change (SR.ps_regs PavlF6P6.ps0) with (map (fun i => (i, nth i PavlF6P6.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF6P6.ps0) with PavlF6P6.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF6P6.regs0 PavlF6P6.regs_out0 60 KS_avlF6P6_0 KS_avlF6P6_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF6P6.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavlF6P6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF6P6.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF6P6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF6P6.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavlF6P6.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    rewrite (BG.out_reg PavlF6P6.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PavlF6P6.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. 
  - right.
    change (SR.ps_pc PavlF6P6.ps1) with 0xb30ec in Hms. change (SR.ps_regs PavlF6P6.ps1) with (map (fun i => (i, nth i PavlF6P6.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF6P6.ps1) with PavlF6P6.cells1 in Hcells. unfold PavlF6P6.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF6P6.regs0 PavlF6P6.regs_out1 60 KS_avlF6P6_1 KS_avlF6P6_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF6P6.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF6P6.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PavlF6P6.regs_out1 E' R' 25 Hregs) by (clear; lia). cbn [nth PavlF6P6.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavlF6P7 := LibSegBa_avlF6P7_b.
Definition KS_avlF6P7_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF6P7.regs0 PavlF6P7.regs_out0).
Lemma KS_avlF6P7_0_ok : BG.kept_ok 60 PavlF6P7.regs0 PavlF6P7.regs_out0 KS_avlF6P7_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF6P7_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF6P7.regs0 PavlF6P7.regs_out1).
Lemma KS_avlF6P7_1_ok : BG.kept_ok 60 PavlF6P7.regs0 PavlF6P7.regs_out1 KS_avlF6P7_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlF6P7_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 18446744073709551615 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 145280 -> getr R (reg 19) = Z_to_bv 64 18446744073709406335 -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 6) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 6) / 8) + 2147450880) 7 -> 0 <= (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7) <= 6 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb30cc M) (st fx' R' 0xb312c M')
        /\ (forall x, In x KS_avlF6P7_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ getr R' (reg 11) = Z_to_bv 64 7
        /\ bv_unsigned (getr R' (reg 12)) = (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7))
      \/ (msteps RSEGS (st fx R 0xb30cc M) (st fx' R' 0xb30ec M')
        /\ (forall x, In x KS_avlF6P7_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavlF6P7.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlF6P7.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlF6P7.kn0).
  { unfold know_ok, PavlF6P7.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlF6P7.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlF6P7.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavlF6P7.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavlF6P7.ps0) with 0xb312c in Hms. change (SR.ps_regs PavlF6P7.ps0) with (map (fun i => (i, nth i PavlF6P7.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF6P7.ps0) with PavlF6P7.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF6P7.regs0 PavlF6P7.regs_out0 60 KS_avlF6P7_0 KS_avlF6P7_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF6P7.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavlF6P7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF6P7.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF6P7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF6P7.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavlF6P7.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    rewrite (BG.out_reg PavlF6P7.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PavlF6P7.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. 
  - right.
    change (SR.ps_pc PavlF6P7.ps1) with 0xb30ec in Hms. change (SR.ps_regs PavlF6P7.ps1) with (map (fun i => (i, nth i PavlF6P7.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF6P7.ps1) with PavlF6P7.cells1 in Hcells. unfold PavlF6P7.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF6P7.regs0 PavlF6P7.regs_out1 60 KS_avlF6P7_1 KS_avlF6P7_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF6P7.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF6P7.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PavlF6P7.regs_out1 E' R' 25 Hregs) by (clear; lia). cbn [nth PavlF6P7.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavlF7Z := LibSegBa_avlF7Z_b.
Definition KS_avlF7Z_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF7Z.regs0 PavlF7Z.regs_out0).
Lemma KS_avlF7Z_0_ok : BG.kept_ok 60 PavlF7Z.regs0 PavlF7Z.regs_out0 KS_avlF7Z_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF7Z_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF7Z.regs0 PavlF7Z.regs_out1).
Lemma KS_avlF7Z_1_ok : BG.kept_ok 60 PavlF7Z.regs0 PavlF7Z.regs_out1 KS_avlF7Z_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlF7Z_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 18446744073709551615 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 145280 -> getr R (reg 19) = Z_to_bv 64 18446744073709406335 -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 7) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5KA.zeros_at M ((((V 33%nat) + 7) / 8) + 2147450880) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb30ec M) (st fx' R' 0xb312c M')
        /\ (forall x, In x KS_avlF7Z_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ getr R' (reg 11) = Z_to_bv 64 0)
      \/ (msteps RSEGS (st fx R 0xb30ec M) (st fx' R' 0xb3234 M')
        /\ (forall x, In x KS_avlF7Z_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 8))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavlF7Z.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlF7Z.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlF7Z.kn0).
  { unfold know_ok, PavlF7Z.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlF7Z.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlF7Z.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavlF7Z.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavlF7Z.ps0) with 0xb312c in Hms. change (SR.ps_regs PavlF7Z.ps0) with (map (fun i => (i, nth i PavlF7Z.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF7Z.ps0) with PavlF7Z.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF7Z.regs0 PavlF7Z.regs_out0 60 KS_avlF7Z_0 KS_avlF7Z_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF7Z.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavlF7Z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PavlF7Z.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF7Z.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
  - right.
    change (SR.ps_pc PavlF7Z.ps1) with 0xb3234 in Hms. change (SR.ps_regs PavlF7Z.ps1) with (map (fun i => (i, nth i PavlF7Z.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF7Z.ps1) with PavlF7Z.cells1 in Hcells. unfold PavlF7Z.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF7Z.regs0 PavlF7Z.regs_out1 60 KS_avlF7Z_1 KS_avlF7Z_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF7Z.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF7Z.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PavlF7Z.regs_out1 E' R' 26 Hregs) by (clear; lia). cbn [nth PavlF7Z.regs_out1]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavlF7P1 := LibSegBa_avlF7P1_b.
Definition KS_avlF7P1_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF7P1.regs0 PavlF7P1.regs_out0).
Lemma KS_avlF7P1_0_ok : BG.kept_ok 60 PavlF7P1.regs0 PavlF7P1.regs_out0 KS_avlF7P1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF7P1_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF7P1.regs0 PavlF7P1.regs_out1).
Lemma KS_avlF7P1_1_ok : BG.kept_ok 60 PavlF7P1.regs0 PavlF7P1.regs_out1 KS_avlF7P1_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlF7P1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 18446744073709551615 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 145280 -> getr R (reg 19) = Z_to_bv 64 18446744073709406335 -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 7) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 7) / 8) + 2147450880) 1 -> 0 <= (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7) <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb30ec M) (st fx' R' 0xb312c M')
        /\ (forall x, In x KS_avlF7P1_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 25) = Z_to_bv 64 0)
      \/ (msteps RSEGS (st fx R 0xb30ec M) (st fx' R' 0xb3234 M')
        /\ (forall x, In x KS_avlF7P1_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ getr R' (reg 25) = Z_to_bv 64 0
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 8))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavlF7P1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlF7P1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlF7P1.kn0).
  { unfold know_ok, PavlF7P1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlF7P1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlF7P1.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavlF7P1.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavlF7P1.ps0) with 0xb312c in Hms. change (SR.ps_regs PavlF7P1.ps0) with (map (fun i => (i, nth i PavlF7P1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF7P1.ps0) with PavlF7P1.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF7P1.regs0 PavlF7P1.regs_out0 60 KS_avlF7P1_0 KS_avlF7P1_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF7P1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavlF7P1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF7P1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF7P1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF7P1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavlF7P1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PavlF7P1.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PavlF7P1.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
  - right.
    change (SR.ps_pc PavlF7P1.ps1) with 0xb3234 in Hms. change (SR.ps_regs PavlF7P1.ps1) with (map (fun i => (i, nth i PavlF7P1.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF7P1.ps1) with PavlF7P1.cells1 in Hcells. unfold PavlF7P1.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF7P1.regs0 PavlF7P1.regs_out1 60 KS_avlF7P1_1 KS_avlF7P1_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF7P1.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF7P1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF7P1.regs_out1 E' R' 25 Hregs) by (clear; lia). cbn [nth PavlF7P1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PavlF7P1.regs_out1 E' R' 26 Hregs) by (clear; lia). cbn [nth PavlF7P1.regs_out1]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavlF7P2 := LibSegBa_avlF7P2_b.
Definition KS_avlF7P2_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF7P2.regs0 PavlF7P2.regs_out0).
Lemma KS_avlF7P2_0_ok : BG.kept_ok 60 PavlF7P2.regs0 PavlF7P2.regs_out0 KS_avlF7P2_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF7P2_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF7P2.regs0 PavlF7P2.regs_out1).
Lemma KS_avlF7P2_1_ok : BG.kept_ok 60 PavlF7P2.regs0 PavlF7P2.regs_out1 KS_avlF7P2_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlF7P2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 18446744073709551615 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 145280 -> getr R (reg 19) = Z_to_bv 64 18446744073709406335 -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 7) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 7) / 8) + 2147450880) 2 -> 0 <= (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb30ec M) (st fx' R' 0xb312c M')
        /\ (forall x, In x KS_avlF7P2_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ bv_unsigned (getr R' (reg 12)) = (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7))
      \/ (msteps RSEGS (st fx R 0xb30ec M) (st fx' R' 0xb3234 M')
        /\ (forall x, In x KS_avlF7P2_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 8))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavlF7P2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlF7P2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlF7P2.kn0).
  { unfold know_ok, PavlF7P2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlF7P2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlF7P2.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavlF7P2.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavlF7P2.ps0) with 0xb312c in Hms. change (SR.ps_regs PavlF7P2.ps0) with (map (fun i => (i, nth i PavlF7P2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF7P2.ps0) with PavlF7P2.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF7P2.regs0 PavlF7P2.regs_out0 60 KS_avlF7P2_0 KS_avlF7P2_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF7P2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavlF7P2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF7P2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF7P2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF7P2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavlF7P2.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    rewrite (BG.out_reg PavlF7P2.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PavlF7P2.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. 
  - right.
    change (SR.ps_pc PavlF7P2.ps1) with 0xb3234 in Hms. change (SR.ps_regs PavlF7P2.ps1) with (map (fun i => (i, nth i PavlF7P2.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF7P2.ps1) with PavlF7P2.cells1 in Hcells. unfold PavlF7P2.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF7P2.regs0 PavlF7P2.regs_out1 60 KS_avlF7P2_1 KS_avlF7P2_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF7P2.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF7P2.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF7P2.regs_out1 E' R' 25 Hregs) by (clear; lia). cbn [nth PavlF7P2.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    rewrite (BG.out_reg PavlF7P2.regs_out1 E' R' 26 Hregs) by (clear; lia). cbn [nth PavlF7P2.regs_out1]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavlF7P3 := LibSegBa_avlF7P3_b.
Definition KS_avlF7P3_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF7P3.regs0 PavlF7P3.regs_out0).
Lemma KS_avlF7P3_0_ok : BG.kept_ok 60 PavlF7P3.regs0 PavlF7P3.regs_out0 KS_avlF7P3_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF7P3_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF7P3.regs0 PavlF7P3.regs_out1).
Lemma KS_avlF7P3_1_ok : BG.kept_ok 60 PavlF7P3.regs0 PavlF7P3.regs_out1 KS_avlF7P3_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlF7P3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 18446744073709551615 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 145280 -> getr R (reg 19) = Z_to_bv 64 18446744073709406335 -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 7) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 7) / 8) + 2147450880) 3 -> 0 <= (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7) <= 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb30ec M) (st fx' R' 0xb312c M')
        /\ (forall x, In x KS_avlF7P3_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ getr R' (reg 11) = Z_to_bv 64 3
        /\ bv_unsigned (getr R' (reg 12)) = (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7))
      \/ (msteps RSEGS (st fx R 0xb30ec M) (st fx' R' 0xb3234 M')
        /\ (forall x, In x KS_avlF7P3_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 8))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavlF7P3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlF7P3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlF7P3.kn0).
  { unfold know_ok, PavlF7P3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlF7P3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlF7P3.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavlF7P3.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavlF7P3.ps0) with 0xb312c in Hms. change (SR.ps_regs PavlF7P3.ps0) with (map (fun i => (i, nth i PavlF7P3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF7P3.ps0) with PavlF7P3.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF7P3.regs0 PavlF7P3.regs_out0 60 KS_avlF7P3_0 KS_avlF7P3_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF7P3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavlF7P3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF7P3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF7P3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF7P3.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavlF7P3.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    rewrite (BG.out_reg PavlF7P3.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PavlF7P3.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. 
  - right.
    change (SR.ps_pc PavlF7P3.ps1) with 0xb3234 in Hms. change (SR.ps_regs PavlF7P3.ps1) with (map (fun i => (i, nth i PavlF7P3.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF7P3.ps1) with PavlF7P3.cells1 in Hcells. unfold PavlF7P3.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF7P3.regs0 PavlF7P3.regs_out1 60 KS_avlF7P3_1 KS_avlF7P3_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF7P3.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF7P3.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF7P3.regs_out1 E' R' 25 Hregs) by (clear; lia). cbn [nth PavlF7P3.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    rewrite (BG.out_reg PavlF7P3.regs_out1 E' R' 26 Hregs) by (clear; lia). cbn [nth PavlF7P3.regs_out1]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavlF7P4 := LibSegBa_avlF7P4_b.
Definition KS_avlF7P4_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF7P4.regs0 PavlF7P4.regs_out0).
Lemma KS_avlF7P4_0_ok : BG.kept_ok 60 PavlF7P4.regs0 PavlF7P4.regs_out0 KS_avlF7P4_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF7P4_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF7P4.regs0 PavlF7P4.regs_out1).
Lemma KS_avlF7P4_1_ok : BG.kept_ok 60 PavlF7P4.regs0 PavlF7P4.regs_out1 KS_avlF7P4_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlF7P4_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 18446744073709551615 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 145280 -> getr R (reg 19) = Z_to_bv 64 18446744073709406335 -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 7) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 7) / 8) + 2147450880) 4 -> 0 <= (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7) <= 3 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb30ec M) (st fx' R' 0xb312c M')
        /\ (forall x, In x KS_avlF7P4_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ getr R' (reg 11) = Z_to_bv 64 4
        /\ bv_unsigned (getr R' (reg 12)) = (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7))
      \/ (msteps RSEGS (st fx R 0xb30ec M) (st fx' R' 0xb3234 M')
        /\ (forall x, In x KS_avlF7P4_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 8))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavlF7P4.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlF7P4.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlF7P4.kn0).
  { unfold know_ok, PavlF7P4.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlF7P4.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlF7P4.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavlF7P4.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavlF7P4.ps0) with 0xb312c in Hms. change (SR.ps_regs PavlF7P4.ps0) with (map (fun i => (i, nth i PavlF7P4.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF7P4.ps0) with PavlF7P4.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF7P4.regs0 PavlF7P4.regs_out0 60 KS_avlF7P4_0 KS_avlF7P4_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF7P4.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavlF7P4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF7P4.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF7P4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF7P4.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavlF7P4.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    rewrite (BG.out_reg PavlF7P4.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PavlF7P4.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. 
  - right.
    change (SR.ps_pc PavlF7P4.ps1) with 0xb3234 in Hms. change (SR.ps_regs PavlF7P4.ps1) with (map (fun i => (i, nth i PavlF7P4.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF7P4.ps1) with PavlF7P4.cells1 in Hcells. unfold PavlF7P4.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF7P4.regs0 PavlF7P4.regs_out1 60 KS_avlF7P4_1 KS_avlF7P4_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF7P4.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF7P4.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF7P4.regs_out1 E' R' 25 Hregs) by (clear; lia). cbn [nth PavlF7P4.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    rewrite (BG.out_reg PavlF7P4.regs_out1 E' R' 26 Hregs) by (clear; lia). cbn [nth PavlF7P4.regs_out1]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavlF7P5 := LibSegBa_avlF7P5_b.
Definition KS_avlF7P5_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF7P5.regs0 PavlF7P5.regs_out0).
Lemma KS_avlF7P5_0_ok : BG.kept_ok 60 PavlF7P5.regs0 PavlF7P5.regs_out0 KS_avlF7P5_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF7P5_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF7P5.regs0 PavlF7P5.regs_out1).
Lemma KS_avlF7P5_1_ok : BG.kept_ok 60 PavlF7P5.regs0 PavlF7P5.regs_out1 KS_avlF7P5_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlF7P5_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 18446744073709551615 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 145280 -> getr R (reg 19) = Z_to_bv 64 18446744073709406335 -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 7) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 7) / 8) + 2147450880) 5 -> 0 <= (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7) <= 4 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb30ec M) (st fx' R' 0xb312c M')
        /\ (forall x, In x KS_avlF7P5_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ getr R' (reg 11) = Z_to_bv 64 5
        /\ bv_unsigned (getr R' (reg 12)) = (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7))
      \/ (msteps RSEGS (st fx R 0xb30ec M) (st fx' R' 0xb3234 M')
        /\ (forall x, In x KS_avlF7P5_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 8))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavlF7P5.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlF7P5.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlF7P5.kn0).
  { unfold know_ok, PavlF7P5.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlF7P5.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlF7P5.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavlF7P5.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavlF7P5.ps0) with 0xb312c in Hms. change (SR.ps_regs PavlF7P5.ps0) with (map (fun i => (i, nth i PavlF7P5.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF7P5.ps0) with PavlF7P5.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF7P5.regs0 PavlF7P5.regs_out0 60 KS_avlF7P5_0 KS_avlF7P5_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF7P5.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavlF7P5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF7P5.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF7P5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF7P5.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavlF7P5.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    rewrite (BG.out_reg PavlF7P5.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PavlF7P5.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. 
  - right.
    change (SR.ps_pc PavlF7P5.ps1) with 0xb3234 in Hms. change (SR.ps_regs PavlF7P5.ps1) with (map (fun i => (i, nth i PavlF7P5.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF7P5.ps1) with PavlF7P5.cells1 in Hcells. unfold PavlF7P5.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF7P5.regs0 PavlF7P5.regs_out1 60 KS_avlF7P5_1 KS_avlF7P5_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF7P5.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF7P5.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF7P5.regs_out1 E' R' 25 Hregs) by (clear; lia). cbn [nth PavlF7P5.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    rewrite (BG.out_reg PavlF7P5.regs_out1 E' R' 26 Hregs) by (clear; lia). cbn [nth PavlF7P5.regs_out1]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavlF7P6 := LibSegBa_avlF7P6_b.
Definition KS_avlF7P6_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF7P6.regs0 PavlF7P6.regs_out0).
Lemma KS_avlF7P6_0_ok : BG.kept_ok 60 PavlF7P6.regs0 PavlF7P6.regs_out0 KS_avlF7P6_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF7P6_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF7P6.regs0 PavlF7P6.regs_out1).
Lemma KS_avlF7P6_1_ok : BG.kept_ok 60 PavlF7P6.regs0 PavlF7P6.regs_out1 KS_avlF7P6_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlF7P6_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 18446744073709551615 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 145280 -> getr R (reg 19) = Z_to_bv 64 18446744073709406335 -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 7) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 7) / 8) + 2147450880) 6 -> 0 <= (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7) <= 5 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb30ec M) (st fx' R' 0xb312c M')
        /\ (forall x, In x KS_avlF7P6_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ bv_unsigned (getr R' (reg 12)) = (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7))
      \/ (msteps RSEGS (st fx R 0xb30ec M) (st fx' R' 0xb3234 M')
        /\ (forall x, In x KS_avlF7P6_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 8))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavlF7P6.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlF7P6.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlF7P6.kn0).
  { unfold know_ok, PavlF7P6.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlF7P6.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlF7P6.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavlF7P6.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavlF7P6.ps0) with 0xb312c in Hms. change (SR.ps_regs PavlF7P6.ps0) with (map (fun i => (i, nth i PavlF7P6.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF7P6.ps0) with PavlF7P6.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF7P6.regs0 PavlF7P6.regs_out0 60 KS_avlF7P6_0 KS_avlF7P6_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF7P6.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavlF7P6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF7P6.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF7P6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF7P6.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavlF7P6.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    rewrite (BG.out_reg PavlF7P6.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PavlF7P6.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. 
  - right.
    change (SR.ps_pc PavlF7P6.ps1) with 0xb3234 in Hms. change (SR.ps_regs PavlF7P6.ps1) with (map (fun i => (i, nth i PavlF7P6.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF7P6.ps1) with PavlF7P6.cells1 in Hcells. unfold PavlF7P6.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF7P6.regs0 PavlF7P6.regs_out1 60 KS_avlF7P6_1 KS_avlF7P6_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF7P6.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF7P6.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF7P6.regs_out1 E' R' 25 Hregs) by (clear; lia). cbn [nth PavlF7P6.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    rewrite (BG.out_reg PavlF7P6.regs_out1 E' R' 26 Hregs) by (clear; lia). cbn [nth PavlF7P6.regs_out1]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavlF7P7 := LibSegBa_avlF7P7_b.
Definition KS_avlF7P7_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF7P7.regs0 PavlF7P7.regs_out0).
Lemma KS_avlF7P7_0_ok : BG.kept_ok 60 PavlF7P7.regs0 PavlF7P7.regs_out0 KS_avlF7P7_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlF7P7_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavlF7P7.regs0 PavlF7P7.regs_out1).
Lemma KS_avlF7P7_1_ok : BG.kept_ok 60 PavlF7P7.regs0 PavlF7P7.regs_out1 KS_avlF7P7_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlF7P7_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 18446744073709551615 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 145280 -> getr R (reg 19) = Z_to_bv 64 18446744073709406335 -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 7) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 7) / 8) + 2147450880) 7 -> 0 <= (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7) <= 6 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb30ec M) (st fx' R' 0xb312c M')
        /\ (forall x, In x KS_avlF7P7_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ getr R' (reg 11) = Z_to_bv 64 7
        /\ bv_unsigned (getr R' (reg 12)) = (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7))
      \/ (msteps RSEGS (st fx R 0xb30ec M) (st fx' R' 0xb3234 M')
        /\ (forall x, In x KS_avlF7P7_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 8))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavlF7P7.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlF7P7.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlF7P7.kn0).
  { unfold know_ok, PavlF7P7.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlF7P7.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlF7P7.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavlF7P7.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavlF7P7.ps0) with 0xb312c in Hms. change (SR.ps_regs PavlF7P7.ps0) with (map (fun i => (i, nth i PavlF7P7.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF7P7.ps0) with PavlF7P7.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF7P7.regs0 PavlF7P7.regs_out0 60 KS_avlF7P7_0 KS_avlF7P7_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF7P7.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavlF7P7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF7P7.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF7P7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF7P7.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavlF7P7.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    rewrite (BG.out_reg PavlF7P7.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PavlF7P7.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. 
  - right.
    change (SR.ps_pc PavlF7P7.ps1) with 0xb3234 in Hms. change (SR.ps_regs PavlF7P7.ps1) with (map (fun i => (i, nth i PavlF7P7.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlF7P7.ps1) with PavlF7P7.cells1 in Hcells. unfold PavlF7P7.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlF7P7.regs0 PavlF7P7.regs_out1 60 KS_avlF7P7_1 KS_avlF7P7_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlF7P7.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlF7P7.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlF7P7.regs_out1 E' R' 25 Hregs) by (clear; lia). cbn [nth PavlF7P7.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    rewrite (BG.out_reg PavlF7P7.regs_out1 E' R' 26 Hregs) by (clear; lia). cbn [nth PavlF7P7.regs_out1]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

End PMAVALP3.
