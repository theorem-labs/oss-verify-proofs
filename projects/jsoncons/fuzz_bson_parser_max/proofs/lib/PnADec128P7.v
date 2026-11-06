(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BigLinkZA.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Ba0PlanKit AsanPlanCore
     BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.seg Require LibSegBa_adkX1 LibSegBa_adkXI LibSegBa_adkXJ LibSegBa_adkXT LibSegBa_adkXN LibSegBa_adkXO LibSegBa_adkXU LibSegBa_adkXC.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNADP7.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).

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
Module PadkX1 := LibSegBa_adkX1.
Definition KS_adkX1_0 : list nat := Eval vm_compute in (BG.kept_list 80 PadkX1.regs0 PadkX1.regs_out0).
Lemma KS_adkX1_0_ok : BG.kept_ok 80 PadkX1.regs0 PadkX1.regs_out0 KS_adkX1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_adkX1_1 : list nat := Eval vm_compute in (BG.kept_list 80 PadkX1.regs0 PadkX1.regs_out1).
Lemma KS_adkX1_1_ok : BG.kept_ok 80 PadkX1.regs0 PadkX1.regs_out1 KS_adkX1_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_adkX1_2 : list nat := Eval vm_compute in (BG.kept_list 80 PadkX1.regs0 PadkX1.regs_out2).
Lemma KS_adkX1_2_ok : BG.kept_ok 80 PadkX1.regs0 PadkX1.regs_out2 KS_adkX1_2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkX1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 35%nat) -> getr R (reg 13) = Z_to_bv 64 (V 39%nat) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 33%nat) + 42) -> getr R (reg 21) = Z_to_bv 64 ((V 33%nat) + (V 44%nat)) -> getr R (reg 22) = Z_to_bv 64 (V 33%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 50%nat) + 32) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 -> getr R (reg 28) = Z_to_bv 64 (V 36%nat) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 50%nat) <= 140737488354816 ->
  4096 <= (V 33%nat) <= 140737488355280 -> 0 <= (V 44%nat) <= 1 -> 0 <= (V 39%nat) <= 4294967295 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb3100 M) (st fx' R' 0xb3140 M')
        /\ (forall x, In x KS_adkX1_0 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 11)) = (((8589934592 * (V 39%nat)) mod 2 ^ 64) / 576460752303423488)
        /\ getr R' (reg 12) = Z_to_bv 64 31
        /\ (((((8589934592 * (V 39%nat)) mod 2 ^ 64) / 576460752303423488) - 31) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0xb3100 M) (st fx' R' 0xb3118 M')
        /\ (forall x, In x KS_adkX1_1 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 11)) = (((8589934592 * (V 39%nat)) mod 2 ^ 64) / 576460752303423488)
        /\ getr R' (reg 12) = Z_to_bv 64 30
        /\ (((((8589934592 * (V 39%nat)) mod 2 ^ 64) / 576460752303423488) - 30) mod 2 ^ 64) < 1
        /\ 1 <= (((((8589934592 * (V 39%nat)) mod 2 ^ 64) / 576460752303423488) - 31) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xb3100 M) (st fx' R' 0xb3168 M')
        /\ (forall x, In x KS_adkX1_2 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 11)) = (((8589934592 * (V 39%nat)) mod 2 ^ 64) / 576460752303423488)
        /\ getr R' (reg 12) = Z_to_bv 64 30
        /\ 1 <= (((((8589934592 * (V 39%nat)) mod 2 ^ 64) / 576460752303423488) - 30) mod 2 ^ 64)
        /\ 1 <= (((((8589934592 * (V 39%nat)) mod 2 ^ 64) / 576460752303423488) - 31) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G13 G18 G19 G20 G21 G22 G23 G26 G27 G28 pvzI8 K1 K2 pvzI9 pvzI10 pvzI11 pvzI12.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV44l; move HV44l before pvzI6; pose proof (proj2 pvzI6) as HV44r; move HV44r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV50l; move HV50l before pvzI7; pose proof (proj2 pvzI7) as HV50r; move HV50r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K4l; move K4l before pvzI10; pose proof (proj2 pvzI10) as K4r; move K4r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K5l; move K5l before pvzI11; pose proof (proj2 pvzI11) as K5r; move K5r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K6l; move K6l before pvzI12; pose proof (proj2 pvzI12) as K6r; move K6r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 39%nat => Z_to_bv 64 vz_39 | 44%nat => Z_to_bv 64 vz_44 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | 39%nat => vz_39 | 44%nat => vz_44 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PadkX1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadkX1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadkX1.kn0).
  { unfold know_ok, PadkX1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV44l HV44r K5l K5r) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadkX1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadkX1.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PadkX1.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PadkX1.ps0) with 0xb3140 in Hms. change (SR.ps_regs PadkX1.ps0) with (map (fun i => (i, nth i PadkX1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PadkX1.ps0) with PadkX1.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkX1.regs0 PadkX1.regs_out0 80 KS_adkX1_0 KS_adkX1_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PadkX1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PadkX1.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PadkX1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PadkX1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. left.
    change (SR.ps_pc PadkX1.ps1) with 0xb3118 in Hms. change (SR.ps_regs PadkX1.ps1) with (map (fun i => (i, nth i PadkX1.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PadkX1.ps1) with PadkX1.cells1 in Hcells. unfold PadkX1.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkX1.regs0 PadkX1.regs_out1 80 KS_adkX1_1 KS_adkX1_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PadkX1.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PadkX1.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PadkX1.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PadkX1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. 
    change (SR.ps_pc PadkX1.ps2) with 0xb3168 in Hms. change (SR.ps_regs PadkX1.ps2) with (map (fun i => (i, nth i PadkX1.regs_out2 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PadkX1.ps2) with PadkX1.cells2 in Hcells. unfold PadkX1.cells2 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkX1.regs0 PadkX1.regs_out2 80 KS_adkX1_2 KS_adkX1_2_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PadkX1.regs_out2 E' R' 11 Hregs) by (clear; lia). cbn [nth PadkX1.regs_out2]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PadkX1.regs_out2 E' R' 12 Hregs) by (clear; lia). cbn [nth PadkX1.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadkXI := LibSegBa_adkXI.
Definition KS_adkXI : list nat := Eval vm_compute in (BG.kept_list 80 PadkXI.regs0 PadkXI.regs_out0).
Lemma KS_adkXI_ok : BG.kept_ok 80 PadkXI.regs0 PadkXI.regs_out0 KS_adkXI = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkXI_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 33%nat) + 42) -> getr R (reg 21) = Z_to_bv 64 ((V 33%nat) + (V 44%nat)) -> getr R (reg 22) = Z_to_bv 64 (V 33%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 50%nat) + 32) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 50%nat) <= 140737488354816 ->
  4096 <= (V 33%nat) <= 140737488355280 -> 0 <= (V 44%nat) <= 1 -> L5.u8_at RSEGS M 6749768 16 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3118 M) (st fx' R' 0x778cc M')
        /\ (forall x, In x KS_adkXI -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 733588
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + (V 44%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 6749769
        /\ getr R' (reg 12) = Z_to_bv 64 8
        /\ getr R' (reg 22) = Z_to_bv 64 6749768).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G18 G19 G20 G21 G22 G23 G26 G27 pvzI5 K1 K2 pvzI6 pvzI7 pvzI8 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV44l; move HV44l before pvzI3; pose proof (proj2 pvzI3) as HV44r; move HV44r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV50l; move HV50l before pvzI4; pose proof (proj2 pvzI4) as HV50r; move HV50r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K4l; move K4l before pvzI7; pose proof (proj2 pvzI7) as K4r; move K4r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K5l; move K5l before pvzI8; pose proof (proj2 pvzI8) as K5r; move K5r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 44%nat => Z_to_bv 64 vz_44 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 44%nat => vz_44 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PadkXI.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadkXI.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadkXI.kn0).
  { unfold know_ok, PadkXI.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV44l HV44r K5l K5r) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadkXI.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadkXI.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PadkXI.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PadkXI.ps0) with 0x778cc in Hms. change (SR.ps_regs PadkXI.ps0) with (map (fun i => (i, nth i PadkXI.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PadkXI.ps0) with PadkXI.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkXI.regs0 PadkXI.regs_out0 80 KS_adkXI KS_adkXI_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PadkXI.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PadkXI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkXI.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkXI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkXI.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PadkXI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkXI.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PadkXI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PadkXI.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PadkXI.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadkXJ := LibSegBa_adkXJ.
Definition KS_adkXJ : list nat := Eval vm_compute in (BG.kept_list 80 PadkXJ.regs0 PadkXJ.regs_out0).
Lemma KS_adkXJ_ok : BG.kept_ok 80 PadkXJ.regs0 PadkXJ.regs_out0 KS_adkXJ = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkXJ_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 33%nat) + 42) -> getr R (reg 21) = Z_to_bv 64 ((V 33%nat) + (V 44%nat)) -> getr R (reg 22) = Z_to_bv 64 6749768 -> getr R (reg 23) = Z_to_bv 64 ((V 50%nat) + 32) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 50%nat) <= 140737488354816 ->
  4096 <= (V 33%nat) <= 140737488355280 -> 0 <= (V 44%nat) <= 1 -> L5.u8_at RSEGS M 6749768 16 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3194 M) (st fx' R' 0xb31c0 M')
        /\ (forall x, In x KS_adkXJ -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 8
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 21) = Z_to_bv 64 (((V 33%nat) + (V 44%nat)) + 8)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G18 G19 G20 G21 G22 G23 G26 G27 pvzI5 K1 K2 pvzI6 pvzI7 pvzI8 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV44l; move HV44l before pvzI3; pose proof (proj2 pvzI3) as HV44r; move HV44r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV50l; move HV50l before pvzI4; pose proof (proj2 pvzI4) as HV50r; move HV50r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K4l; move K4l before pvzI7; pose proof (proj2 pvzI7) as K4r; move K4r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K5l; move K5l before pvzI8; pose proof (proj2 pvzI8) as K5r; move K5r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 44%nat => Z_to_bv 64 vz_44 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 44%nat => vz_44 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PadkXJ.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadkXJ.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadkXJ.kn0).
  { unfold know_ok, PadkXJ.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV44l HV44r K5l K5r) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadkXJ.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadkXJ.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PadkXJ.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PadkXJ.ps0) with 0xb31c0 in Hms. change (SR.ps_regs PadkXJ.ps0) with (map (fun i => (i, nth i PadkXJ.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PadkXJ.ps0) with PadkXJ.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkXJ.regs0 PadkXJ.regs_out0 80 KS_adkXJ KS_adkXJ_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PadkXJ.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkXJ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkXJ.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PadkXJ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PadkXJ.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PadkXJ.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadkXT := LibSegBa_adkXT.
Definition KS_adkXT : list nat := Eval vm_compute in (BG.kept_list 80 PadkXT.regs0 PadkXT.regs_out0).
Lemma KS_adkXT_ok : BG.kept_ok 80 PadkXT.regs0 PadkXT.regs_out0 KS_adkXT = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkXT_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 21) = Z_to_bv 64 (V 52%nat) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 50%nat) <= 140737488354816 ->
  4096 <= (V 52%nat) <= 140737488355320 -> L5KA.zeros_at M (((V 52%nat) / 8) + 2147450880) 1 -> L5.writable RSEGS M (V 52%nat) 1 -> (2147446784 + 17592186048512 <= (V 52%nat) \/ (V 52%nat) + 1 <= 2147446784) ->
  (((V 2%nat) - 128) + 128 <= (V 52%nat) \/ (V 52%nat) + 1 <= ((V 2%nat) - 128)) -> (65536 + 6832128 <= (V 52%nat) \/ (V 52%nat) + 1 <= 65536) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 52%nat) + 0) <= bv_unsigned a < ((V 52%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 52%nat) + 0) <= i < ((V 52%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb31c0 M) (st fx' R' 0xb2fa4 M')
        /\ (forall x, In x KS_adkXT -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 24) = Z_to_bv 64 0
        /\ L5.u8_at RSEGS M' (V 52%nat) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G8 G9 G18 G19 G21 G26 G27 pvzI4 K1 K2 pvzI5 pvzI6 K5 K6 K7 K8 K9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV50l; move HV50l before pvzI2; pose proof (proj2 pvzI2) as HV50r; move HV50r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV52l; move HV52l before pvzI3; pose proof (proj2 pvzI3) as HV52r; move HV52r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K3l; move K3l before pvzI5; pose proof (proj2 pvzI5) as K3r; move K3r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K4l; move K4l before pvzI6; pose proof (proj2 pvzI6) as K4r; move K4r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_52 := V 52%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 50%nat => Z_to_bv 64 vz_50 | 52%nat => Z_to_bv 64 vz_52 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 50%nat => vz_50 | 52%nat => vz_52 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 53%nat. }
  assert (HR: regs_ok E PadkXT.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadkXT.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadkXT.kn0).
  { unfold know_ok, PadkXT.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K8; lia | clear - HV2l HV2r K0l K0r K8; lia | clear - HV2l HV2r K0l K0r K8; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV52l HV52r K4l K4r K7 K8 K9) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV52l HV52r K4l K4r K7 K8 K9) | evalEk ZA ltac:(clear) | clear - HV52l HV52r K4l K4r K7 K8 K9; lia | clear - HV52l HV52r K4l K4r K7 K8 K9; lia | clear - HV52l HV52r K4l K4r K7 K8 K9; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV52l HV52r K4l K4r K7 K8 K9) | evalEk ZA ltac:(clear) | clear - HV52l HV52r K4l K4r K7 K8 K9; lia | clear - HV52l HV52r K4l K4r K7 K8 K9; lia | clear - HV52l HV52r K4l K4r K7 K8 K9; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV52l HV52r K4l K4r K7 K8 K9) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV52l HV52r K4l K4r K7 K8 K9) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV52l HV52r K4l K4r K7 K8 K9) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadkXT.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadkXT.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_52 + 0) <= bv_unsigned a < (vz_52 + 0) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PadkXT.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV52l HV52r K4l K4r K7 K8 K9) | evalEk' ZA Hag ltac:(clear) | clear - HV52l HV52r K4l K4r K7 K8 K9 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PadkXT.ps0) with 0xb2fa4 in Hms. change (SR.ps_regs PadkXT.ps0) with (map (fun i => (i, nth i PadkXT.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PadkXT.ps0) with PadkXT.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkXT.regs0 PadkXT.regs_out0 80 KS_adkXT KS_adkXT_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PadkXT.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkXT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkXT.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PadkXT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV52l HV52r K4l K4r K7 K8 K9) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadkXN := LibSegBa_adkXN.
Definition KS_adkXN : list nat := Eval vm_compute in (BG.kept_list 80 PadkXN.regs0 PadkXN.regs_out0).
Lemma KS_adkXN_ok : BG.kept_ok 80 PadkXN.regs0 PadkXN.regs_out0 KS_adkXN = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkXN_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 33%nat) + 42) -> getr R (reg 21) = Z_to_bv 64 ((V 33%nat) + (V 44%nat)) -> getr R (reg 22) = Z_to_bv 64 (V 33%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 50%nat) + 32) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 50%nat) <= 140737488354816 ->
  4096 <= (V 33%nat) <= 140737488355280 -> 0 <= (V 44%nat) <= 1 -> L5.u8_at RSEGS M 6749800 6 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3140 M) (st fx' R' 0x778cc M')
        /\ (forall x, In x KS_adkXN -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 733680
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 6749801
        /\ getr R' (reg 12) = Z_to_bv 64 3
        /\ getr R' (reg 21) = Z_to_bv 64 6749800).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G18 G19 G20 G21 G22 G23 G26 G27 pvzI5 K1 K2 pvzI6 pvzI7 pvzI8 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV44l; move HV44l before pvzI3; pose proof (proj2 pvzI3) as HV44r; move HV44r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV50l; move HV50l before pvzI4; pose proof (proj2 pvzI4) as HV50r; move HV50r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K4l; move K4l before pvzI7; pose proof (proj2 pvzI7) as K4r; move K4r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K5l; move K5l before pvzI8; pose proof (proj2 pvzI8) as K5r; move K5r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 44%nat => Z_to_bv 64 vz_44 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 44%nat => vz_44 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PadkXN.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadkXN.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadkXN.kn0).
  { unfold know_ok, PadkXN.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV44l HV44r K5l K5r) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadkXN.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadkXN.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PadkXN.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PadkXN.ps0) with 0x778cc in Hms. change (SR.ps_regs PadkXN.ps0) with (map (fun i => (i, nth i PadkXN.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PadkXN.ps0) with PadkXN.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkXN.regs0 PadkXN.regs_out0 80 KS_adkXN KS_adkXN_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PadkXN.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PadkXN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkXN.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkXN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkXN.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PadkXN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkXN.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PadkXN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PadkXN.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PadkXN.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadkXO := LibSegBa_adkXO.
Definition KS_adkXO : list nat := Eval vm_compute in (BG.kept_list 80 PadkXO.regs0 PadkXO.regs_out0).
Lemma KS_adkXO_ok : BG.kept_ok 80 PadkXO.regs0 PadkXO.regs_out0 KS_adkXO = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkXO_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 33%nat) + 42) -> getr R (reg 21) = Z_to_bv 64 6749800 -> getr R (reg 22) = Z_to_bv 64 (V 33%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 50%nat) + 32) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 50%nat) <= 140737488354816 ->
  4096 <= (V 33%nat) <= 140737488355280 -> 0 <= (V 44%nat) <= 1 -> L5.u8_at RSEGS M 6749800 6 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb31f0 M) (st fx' R' 0xb320c M')
        /\ (forall x, In x KS_adkXO -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 6
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 33%nat) + 3)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G18 G19 G20 G21 G22 G23 G26 G27 pvzI5 K1 K2 pvzI6 pvzI7 pvzI8 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV44l; move HV44l before pvzI3; pose proof (proj2 pvzI3) as HV44r; move HV44r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV50l; move HV50l before pvzI4; pose proof (proj2 pvzI4) as HV50r; move HV50r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K4l; move K4l before pvzI7; pose proof (proj2 pvzI7) as K4r; move K4r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K5l; move K5l before pvzI8; pose proof (proj2 pvzI8) as K5r; move K5r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 44%nat => Z_to_bv 64 vz_44 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 44%nat => vz_44 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PadkXO.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadkXO.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadkXO.kn0).
  { unfold know_ok, PadkXO.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV44l HV44r K5l K5r) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadkXO.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadkXO.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PadkXO.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PadkXO.ps0) with 0xb320c in Hms. change (SR.ps_regs PadkXO.ps0) with (map (fun i => (i, nth i PadkXO.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PadkXO.ps0) with PadkXO.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkXO.regs0 PadkXO.regs_out0 80 KS_adkXO KS_adkXO_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PadkXO.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkXO.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkXO.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PadkXO.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PadkXO.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PadkXO.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadkXU := LibSegBa_adkXU.
Definition KS_adkXU : list nat := Eval vm_compute in (BG.kept_list 80 PadkXU.regs0 PadkXU.regs_out0).
Lemma KS_adkXU_ok : BG.kept_ok 80 PadkXU.regs0 PadkXU.regs_out0 KS_adkXU = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkXU_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 21) = Z_to_bv 64 (V 52%nat) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 50%nat) <= 140737488354816 ->
  4096 <= (V 52%nat) <= 140737488355320 -> L5KA.zeros_at M (((V 52%nat) / 8) + 2147450880) 1 -> L5.writable RSEGS M (V 52%nat) 1 -> (2147446784 + 17592186048512 <= (V 52%nat) \/ (V 52%nat) + 1 <= 2147446784) ->
  (((V 2%nat) - 128) + 128 <= (V 52%nat) \/ (V 52%nat) + 1 <= ((V 2%nat) - 128)) -> (65536 + 6832128 <= (V 52%nat) \/ (V 52%nat) + 1 <= 65536) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 52%nat) + 0) <= bv_unsigned a < ((V 52%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 52%nat) + 0) <= i < ((V 52%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb320c M) (st fx' R' 0xb2fa4 M')
        /\ (forall x, In x KS_adkXU -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 24) = Z_to_bv 64 0
        /\ L5.u8_at RSEGS M' (V 52%nat) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G8 G9 G18 G19 G21 G26 G27 pvzI4 K1 K2 pvzI5 pvzI6 K5 K6 K7 K8 K9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV50l; move HV50l before pvzI2; pose proof (proj2 pvzI2) as HV50r; move HV50r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV52l; move HV52l before pvzI3; pose proof (proj2 pvzI3) as HV52r; move HV52r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K3l; move K3l before pvzI5; pose proof (proj2 pvzI5) as K3r; move K3r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K4l; move K4l before pvzI6; pose proof (proj2 pvzI6) as K4r; move K4r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_52 := V 52%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 50%nat => Z_to_bv 64 vz_50 | 52%nat => Z_to_bv 64 vz_52 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 50%nat => vz_50 | 52%nat => vz_52 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 53%nat. }
  assert (HR: regs_ok E PadkXU.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadkXU.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadkXU.kn0).
  { unfold know_ok, PadkXU.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K8; lia | clear - HV2l HV2r K0l K0r K8; lia | clear - HV2l HV2r K0l K0r K8; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV52l HV52r K4l K4r K7 K8 K9) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV52l HV52r K4l K4r K7 K8 K9) | evalEk ZA ltac:(clear) | clear - HV52l HV52r K4l K4r K7 K8 K9; lia | clear - HV52l HV52r K4l K4r K7 K8 K9; lia | clear - HV52l HV52r K4l K4r K7 K8 K9; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV52l HV52r K4l K4r K7 K8 K9) | evalEk ZA ltac:(clear) | clear - HV52l HV52r K4l K4r K7 K8 K9; lia | clear - HV52l HV52r K4l K4r K7 K8 K9; lia | clear - HV52l HV52r K4l K4r K7 K8 K9; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV52l HV52r K4l K4r K7 K8 K9) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV52l HV52r K4l K4r K7 K8 K9) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV52l HV52r K4l K4r K7 K8 K9) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadkXU.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadkXU.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_52 + 0) <= bv_unsigned a < (vz_52 + 0) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PadkXU.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV52l HV52r K4l K4r K7 K8 K9) | evalEk' ZA Hag ltac:(clear) | clear - HV52l HV52r K4l K4r K7 K8 K9 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PadkXU.ps0) with 0xb2fa4 in Hms. change (SR.ps_regs PadkXU.ps0) with (map (fun i => (i, nth i PadkXU.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PadkXU.ps0) with PadkXU.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkXU.regs0 PadkXU.regs_out0 80 KS_adkXU KS_adkXU_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PadkXU.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkXU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkXU.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PadkXU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV52l HV52r K4l K4r K7 K8 K9) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadkXC := LibSegBa_adkXC.
Definition KS_adkXC_0 : list nat := Eval vm_compute in (BG.kept_list 80 PadkXC.regs0 PadkXC.regs_out0).
Lemma KS_adkXC_0_ok : BG.kept_ok 80 PadkXC.regs0 PadkXC.regs_out0 KS_adkXC_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_adkXC_1 : list nat := Eval vm_compute in (BG.kept_list 80 PadkXC.regs0 PadkXC.regs_out1).
Lemma KS_adkXC_1_ok : BG.kept_ok 80 PadkXC.regs0 PadkXC.regs_out1 KS_adkXC_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_adkXC_2 : list nat := Eval vm_compute in (BG.kept_list 80 PadkXC.regs0 PadkXC.regs_out2).
Lemma KS_adkXC_2_ok : BG.kept_ok 80 PadkXC.regs0 PadkXC.regs_out2 KS_adkXC_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_adkXC_3 : list nat := Eval vm_compute in (BG.kept_list 80 PadkXC.regs0 PadkXC.regs_out3).
Lemma KS_adkXC_3_ok : BG.kept_ok 80 PadkXC.regs0 PadkXC.regs_out3 KS_adkXC_3 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_adkXC_4 : list nat := Eval vm_compute in (BG.kept_list 80 PadkXC.regs0 PadkXC.regs_out4).
Lemma KS_adkXC_4_ok : BG.kept_ok 80 PadkXC.regs0 PadkXC.regs_out4 KS_adkXC_4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkXC_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 35%nat) -> getr R (reg 13) = Z_to_bv 64 (V 39%nat) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 33%nat) + 42) -> getr R (reg 21) = Z_to_bv 64 ((V 33%nat) + (V 44%nat)) -> getr R (reg 22) = Z_to_bv 64 (V 33%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 50%nat) + 32) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 -> getr R (reg 28) = Z_to_bv 64 (V 36%nat) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 50%nat) <= 140737488354816 ->
  4096 <= (V 33%nat) <= 140737488355280 -> 0 <= (V 44%nat) <= 1 -> L5.img_clear M 65536 1269760 -> 0 <= (V 39%nat) <= 4294967295 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb3168 M) (st fx' R' 0xb2aec M')
        /\ (forall x, In x KS_adkXC_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAluw Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_OR (EMd Instr.M_MUL (ELit 4294967296) (EVar 35)) (EAlu Instr.ALU_SRL (EVar 35) (ELit 32))) (EVar 35)) (ELit 0))
        /\ bv_unsigned (getr R' (reg 11)) = ((V 39%nat) / 32768)
        /\ getr R' (reg 12) = Z_to_bv 64 16383
        /\ bv_unsigned (getr R' (reg 13)) = ((4294967296 * (V 35%nat)) mod 2 ^ 64)
        /\ bv_unsigned (getr R' (reg 14)) = (((((131072 * (V 36%nat)) mod 2 ^ 64) / 9223372036854775808) + 8) mod 2 ^ 64)
        /\ getr R' (reg 15) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAluw Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 16384) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 131072) (EVar 36)) (ELit 63))) (EAlu Instr.ALU_AND (EVar 39) (ELit 16383))) (ELit 131072)) (EVar 36)) (ELit 0))
        /\ bv_unsigned (getr R' (reg 16)) = ((V 35%nat) / 4294967296)
        /\ bv_unsigned (getr R' (reg 29)) = (Z.lor ((4294967296 * (V 35%nat)) mod 2 ^ 64) ((V 35%nat) / 4294967296))
        /\ bv_unsigned (getr R' (reg 30)) = ((((((16384 * (((131072 * (V 36%nat)) mod 2 ^ 64) / 9223372036854775808)) mod 2 ^ 64) + (Z.land (V 39%nat) 16383)) mod 2 ^ 64) + 131072) mod 2 ^ 64)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_OR (EMd Instr.M_MUL (ELit 4294967296) (EVar 35)) (EAlu Instr.ALU_SRL (EVar 35) (ELit 32))) (EVar 35)) (ELit 0)) (ELit 0)) (ELit 1))) <= 1
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 16384) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 131072) (EVar 36)) (ELit 63))) (EAlu Instr.ALU_AND (EVar 39) (ELit 16383))) (ELit 131072)) (EVar 36)) (ELit 0)) (ELit 0)) (ELit 1))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb3168 M) (st fx' R' 0xb2aec M')
        /\ (forall x, In x KS_adkXC_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 7
        /\ bv_unsigned (getr R' (reg 11)) = ((V 39%nat) / 32768)
        /\ getr R' (reg 12) = Z_to_bv 64 16383
        /\ bv_unsigned (getr R' (reg 13)) = ((4294967296 * (V 35%nat)) mod 2 ^ 64)
        /\ bv_unsigned (getr R' (reg 14)) = (((((131072 * (V 36%nat)) mod 2 ^ 64) / 9223372036854775808) + 8) mod 2 ^ 64)
        /\ getr R' (reg 15) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAluw Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 16384) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 131072) (EVar 36)) (ELit 63))) (EAlu Instr.ALU_AND (EVar 39) (ELit 16383))) (ELit 131072)) (EVar 36)) (ELit 0))
        /\ bv_unsigned (getr R' (reg 16)) = ((V 35%nat) / 4294967296)
        /\ bv_unsigned (getr R' (reg 29)) = (Z.lor ((4294967296 * (V 35%nat)) mod 2 ^ 64) ((V 35%nat) / 4294967296))
        /\ bv_unsigned (getr R' (reg 30)) = ((((((16384 * (((131072 * (V 36%nat)) mod 2 ^ 64) / 9223372036854775808)) mod 2 ^ 64) + (Z.land (V 39%nat) 16383)) mod 2 ^ 64) + 131072) mod 2 ^ 64)
        /\ 7 < (((((131072 * (V 36%nat)) mod 2 ^ 64) / 9223372036854775808) + 8) mod 2 ^ 64)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_OR (EMd Instr.M_MUL (ELit 4294967296) (EVar 35)) (EAlu Instr.ALU_SRL (EVar 35) (ELit 32))) (EVar 35)) (ELit 0)) (ELit 0)) (ELit 1))) <= 0
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 16384) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 131072) (EVar 36)) (ELit 63))) (EAlu Instr.ALU_AND (EVar 39) (ELit 16383))) (ELit 131072)) (EVar 36)) (ELit 0)) (ELit 0)) (ELit 1))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb3168 M) (st fx' R' 0xb2aec M')
        /\ (forall x, In x KS_adkXC_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 7
        /\ bv_unsigned (getr R' (reg 11)) = ((V 39%nat) / 32768)
        /\ getr R' (reg 12) = Z_to_bv 64 16383
        /\ bv_unsigned (getr R' (reg 13)) = ((4294967296 * (V 35%nat)) mod 2 ^ 64)
        /\ bv_unsigned (getr R' (reg 14)) = (((((131072 * (V 36%nat)) mod 2 ^ 64) / 9223372036854775808) + 8) mod 2 ^ 64)
        /\ getr R' (reg 15) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAluw Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 16384) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 131072) (EVar 36)) (ELit 63))) (EAlu Instr.ALU_AND (EVar 39) (ELit 16383))) (ELit 131072)) (EVar 36)) (ELit 0))
        /\ bv_unsigned (getr R' (reg 16)) = ((V 35%nat) / 4294967296)
        /\ bv_unsigned (getr R' (reg 29)) = (Z.lor ((4294967296 * (V 35%nat)) mod 2 ^ 64) ((V 35%nat) / 4294967296))
        /\ bv_unsigned (getr R' (reg 30)) = ((((((16384 * (((131072 * (V 36%nat)) mod 2 ^ 64) / 9223372036854775808)) mod 2 ^ 64) + (Z.land (V 39%nat) 16383)) mod 2 ^ 64) + 131072) mod 2 ^ 64)
        /\ 7 < (((((131072 * (V 36%nat)) mod 2 ^ 64) / 9223372036854775808) + 8) mod 2 ^ 64)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 16384) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 131072) (EVar 36)) (ELit 63))) (EAlu Instr.ALU_AND (EVar 39) (ELit 16383))) (ELit 131072)) (EVar 36)) (ELit 0)) (ELit 0)) (ELit 1))) <= 0)
      \/ (msteps RSEGS (st fx R 0xb3168 M) (st fx' R' 0xb2a14 M')
        /\ (forall x, In x KS_adkXC_3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 14757395259826634752
        /\ getr R' (reg 6) = Z_to_bv 64 10
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ bv_unsigned (getr R' (reg 11)) = ((V 39%nat) / 32768)
        /\ getr R' (reg 12) = Z_to_bv 64 16383
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 50%nat) + 172)
        /\ getr R' (reg 15) = Z_to_bv 64 18446744073709551580
        /\ getr R' (reg 16) = Z_to_bv 64 19342813113834067
        /\ getr R' (reg 17) = Z_to_bv 64 1000000000
        /\ bv_unsigned (getr R' (reg 29)) = (Z.lor ((4294967296 * (V 35%nat)) mod 2 ^ 64) ((V 35%nat) / 4294967296))
        /\ bv_unsigned (getr R' (reg 30)) = ((((((16384 * (((131072 * (V 36%nat)) mod 2 ^ 64) / 9223372036854775808)) mod 2 ^ 64) + (Z.land (V 39%nat) 16383)) mod 2 ^ 64) + 131072) mod 2 ^ 64)
        /\ getr R' (reg 31) = Z_to_bv 64 3
        /\ (((((131072 * (V 36%nat)) mod 2 ^ 64) / 9223372036854775808) + 8) mod 2 ^ 64) <= 7
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_OR (EMd Instr.M_MUL (ELit 4294967296) (EVar 35)) (EAlu Instr.ALU_SRL (EVar 35) (ELit 32))) (EVar 35)) (ELit 0)) (ELit 0)) (ELit 1))) <= 0
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 16384) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 131072) (EVar 36)) (ELit 63))) (EAlu Instr.ALU_AND (EVar 39) (ELit 16383))) (ELit 131072)) (EVar 36)) (ELit 0)) (ELit 0)) (ELit 1))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb3168 M) (st fx' R' 0xb2a14 M')
        /\ (forall x, In x KS_adkXC_4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 14757395259826634752
        /\ getr R' (reg 6) = Z_to_bv 64 10
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ bv_unsigned (getr R' (reg 11)) = ((V 39%nat) / 32768)
        /\ getr R' (reg 12) = Z_to_bv 64 16383
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 50%nat) + 172)
        /\ getr R' (reg 15) = Z_to_bv 64 18446744073709551580
        /\ getr R' (reg 16) = Z_to_bv 64 19342813113834067
        /\ getr R' (reg 17) = Z_to_bv 64 1000000000
        /\ bv_unsigned (getr R' (reg 29)) = (Z.lor ((4294967296 * (V 35%nat)) mod 2 ^ 64) ((V 35%nat) / 4294967296))
        /\ bv_unsigned (getr R' (reg 30)) = ((((((16384 * (((131072 * (V 36%nat)) mod 2 ^ 64) / 9223372036854775808)) mod 2 ^ 64) + (Z.land (V 39%nat) 16383)) mod 2 ^ 64) + 131072) mod 2 ^ 64)
        /\ getr R' (reg 31) = Z_to_bv 64 3
        /\ (((((131072 * (V 36%nat)) mod 2 ^ 64) / 9223372036854775808) + 8) mod 2 ^ 64) <= 7
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 16384) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 131072) (EVar 36)) (ELit 63))) (EAlu Instr.ALU_AND (EVar 39) (ELit 16383))) (ELit 131072)) (EVar 36)) (ELit 0)) (ELit 0)) (ELit 1))) <= 0)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G13 G18 G19 G20 G21 G22 G23 G26 G27 G28 pvzI8 K1 K2 pvzI9 pvzI10 pvzI11 K6 pvzI12.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV44l; move HV44l before pvzI6; pose proof (proj2 pvzI6) as HV44r; move HV44r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV50l; move HV50l before pvzI7; pose proof (proj2 pvzI7) as HV50r; move HV50r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K4l; move K4l before pvzI10; pose proof (proj2 pvzI10) as K4r; move K4r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K5l; move K5l before pvzI11; pose proof (proj2 pvzI11) as K5r; move K5r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K7l; move K7l before pvzI12; pose proof (proj2 pvzI12) as K7r; move K7r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 39%nat => Z_to_bv 64 vz_39 | 44%nat => Z_to_bv 64 vz_44 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | 39%nat => vz_39 | 44%nat => vz_44 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PadkXC.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadkXC.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadkXC.kn0).
  { unfold know_ok, PadkXC.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV44l HV44r K5l K5r) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadkXC.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadkXC.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PadkXC.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PadkXC.ps0) with 0xb2aec in Hms. change (SR.ps_regs PadkXC.ps0) with (map (fun i => (i, nth i PadkXC.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PadkXC.ps0) with PadkXC.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkXC.regs0 PadkXC.regs_out0 80 KS_adkXC_0 KS_adkXC_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PadkXC.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    split. { rewrite (BG.out_reg PadkXC.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PadkXC.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkXC.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PadkXC.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PadkXC.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    split. { rewrite (BG.out_reg PadkXC.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PadkXC.regs_out0 E' R' 29 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PadkXC.regs_out0 E' R' 30 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. left.
    change (SR.ps_pc PadkXC.ps1) with 0xb2aec in Hms. change (SR.ps_regs PadkXC.ps1) with (map (fun i => (i, nth i PadkXC.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PadkXC.ps1) with PadkXC.cells1 in Hcells. unfold PadkXC.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkXC.regs0 PadkXC.regs_out1 80 KS_adkXC_1 KS_adkXC_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PadkXC.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkXC.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PadkXC.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkXC.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PadkXC.regs_out1 E' R' 14 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PadkXC.regs_out1 E' R' 15 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out1]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    split. { rewrite (BG.out_reg PadkXC.regs_out1 E' R' 16 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PadkXC.regs_out1 E' R' 29 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PadkXC.regs_out1 E' R' 30 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. left.
    change (SR.ps_pc PadkXC.ps2) with 0xb2aec in Hms. change (SR.ps_regs PadkXC.ps2) with (map (fun i => (i, nth i PadkXC.regs_out2 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PadkXC.ps2) with PadkXC.cells2 in Hcells. unfold PadkXC.cells2 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkXC.regs0 PadkXC.regs_out2 80 KS_adkXC_2 KS_adkXC_2_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PadkXC.regs_out2 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkXC.regs_out2 E' R' 11 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out2]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PadkXC.regs_out2 E' R' 12 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkXC.regs_out2 E' R' 13 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out2]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PadkXC.regs_out2 E' R' 14 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out2]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PadkXC.regs_out2 E' R' 15 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out2]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    split. { rewrite (BG.out_reg PadkXC.regs_out2 E' R' 16 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out2]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PadkXC.regs_out2 E' R' 29 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out2]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PadkXC.regs_out2 E' R' 30 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out2]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. left.
    change (SR.ps_pc PadkXC.ps3) with 0xb2a14 in Hms. change (SR.ps_regs PadkXC.ps3) with (map (fun i => (i, nth i PadkXC.regs_out3 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PadkXC.ps3) with PadkXC.cells3 in Hcells. unfold PadkXC.cells3 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkXC.regs0 PadkXC.regs_out3 80 KS_adkXC_3 KS_adkXC_3_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PadkXC.regs_out3 E' R' 5 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkXC.regs_out3 E' R' 6 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkXC.regs_out3 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkXC.regs_out3 E' R' 11 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out3]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PadkXC.regs_out3 E' R' 12 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkXC.regs_out3 E' R' 13 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkXC.regs_out3 E' R' 14 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkXC.regs_out3 E' R' 15 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkXC.regs_out3 E' R' 16 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkXC.regs_out3 E' R' 17 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkXC.regs_out3 E' R' 29 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out3]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PadkXC.regs_out3 E' R' 30 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out3]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PadkXC.regs_out3 E' R' 31 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. 
    change (SR.ps_pc PadkXC.ps4) with 0xb2a14 in Hms. change (SR.ps_regs PadkXC.ps4) with (map (fun i => (i, nth i PadkXC.regs_out4 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PadkXC.ps4) with PadkXC.cells4 in Hcells. unfold PadkXC.cells4 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkXC.regs0 PadkXC.regs_out4 80 KS_adkXC_4 KS_adkXC_4_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PadkXC.regs_out4 E' R' 5 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkXC.regs_out4 E' R' 6 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkXC.regs_out4 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkXC.regs_out4 E' R' 11 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out4]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PadkXC.regs_out4 E' R' 12 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkXC.regs_out4 E' R' 13 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkXC.regs_out4 E' R' 14 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkXC.regs_out4 E' R' 15 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkXC.regs_out4 E' R' 16 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkXC.regs_out4 E' R' 17 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkXC.regs_out4 E' R' 29 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out4]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PadkXC.regs_out4 E' R' 30 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out4]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PadkXC.regs_out4 E' R' 31 Hregs) by (clear; lia). cbn [nth PadkXC.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. 
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.
(* [comment removed for export] *)

End PNADP7.
