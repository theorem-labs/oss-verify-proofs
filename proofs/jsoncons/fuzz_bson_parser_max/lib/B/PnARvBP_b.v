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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require LibSegBa_awvY1a_b LibSegBa_awvY1b_b LibSegBa_awvY1c_b LibSegBa_awvY2_b LibSegBa_awvY2c_b LibSegBa_awvY3a_b LibSegBa_awvY3b_b LibSegBa_awvY3c_b LibSegBa_awvY4a_b LibSegBa_awvY4b_b LibSegBa_awvY4c_b LibSegBa_awvY5a_b LibSegBa_awvY5b_b LibSegBa_awvY5c_b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNARVBP.
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
Module PawvY1a := LibSegBa_awvY1a_b.
Definition KS_awvY1a : list nat := Eval vm_compute in (BG.kept_list 80 PawvY1a.regs0 PawvY1a.regs_out0).
Lemma KS_awvY1a_ok : BG.kept_ok 80 PawvY1a.regs0 PawvY1a.regs_out0 KS_awvY1a = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvY1a_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  140735332487392 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 -> 6905856 <= (V 50%nat) <= 140737488354816 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 512 ->
  L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 50%nat) + 504) (V 51%nat) ->
  4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 512 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) ->
  (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> (65536 + 6840320 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) -> (65536 + 6840320 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= 65536) ->
  (65536 + 6840320 <= (V 51%nat) \/ (V 51%nat) + 1 <= 65536) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 136) <= bv_unsigned a < ((V 2%nat) - 136) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 40) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 40) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 136) <= i < ((V 2%nat) - 136) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 40) <= i < ((((V 50%nat) / 8) + 2147450880) + 40) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb08a4 M) (st fx' R' 0xaed4c M')
        /\ (forall x, In x KS_awvY1a -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 723140
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 50%nat) + 320)
        /\ getr R' (reg 12) = Z_to_bv 64 4
        /\ getr R' (reg 24) = Z_to_bv 64 ((V 50%nat) + 320)
        /\ getr R' (reg 25) = getr R (reg 25)
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450920) 4
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) ((V 33%nat) + 16)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G18 G19 G20 G21 G22 G26 G27 pvzI7 K1 K2 pvzI8 K4 pvzI9 K6 K7 K8 K9 K10 K11 pvzI10 K13 K14 K15 K16 K17 K18 K19 K20.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K5l; move K5l before pvzI9; pose proof (proj2 pvzI9) as K5r; move K5r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K12l; move K12l before pvzI10; pose proof (proj2 pvzI10) as K12r; move K12r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PawvY1a.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvY1a.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvY1a.kn0).
  { unfold know_ok, PawvY1a.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K17) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K17) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K17) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K17; lia | clear - HV2l HV2r K0l K0r K16 K17; lia | clear - HV2l HV2r K0l K0r K16 K17; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | clear; lia | exact K6]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19; lia | clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19; lia | clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19; lia | clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19; lia | clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19; lia | clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19; lia | clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk ZA ltac:(clear - HV51l HV51r K12l K12r K14 K15 K17 K20) | clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19; lia | clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K12l K12r K14 K15 K17 K20) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K12l K12r K14 K15 K17 K20) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K12l K12r K14 K15 K17 K20; lia | clear - HV51l HV51r K12l K12r K14 K15 K17 K20; lia | clear - HV51l HV51r K12l K12r K14 K15 K17 K20; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K12l K12r K14 K15 K17 K20) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K12l K12r K14 K15 K17 K20) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K12l K12r K14 K15 K17 K20) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K12l K12r K14 K15 K17 K20) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvY1a.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvY1a.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 136) <= bv_unsigned a < (vz_2 - 136) + 8) -> ~ ((((vz_50 / 8) + 2147450880) + 40) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 40) + 1) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PawvY1a.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K17 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvY1a.ps0) with 0xaed4c in Hms. change (SR.ps_regs PawvY1a.ps0) with (map (fun i => (i, nth i PawvY1a.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvY1a.ps0) with PawvY1a.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvY1a.regs0 PawvY1a.regs_out0 80 KS_awvY1a KS_awvY1a_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvY1a.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PawvY1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvY1a.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvY1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvY1a.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvY1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvY1a.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PawvY1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvY1a.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PawvY1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvY1a.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PawvY1a.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K17) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvY1b := LibSegBa_awvY1b_b.
Definition KS_awvY1b_0 : list nat := Eval vm_compute in (BG.kept_list 80 PawvY1b.regs0 PawvY1b.regs_out0).
Lemma KS_awvY1b_0_ok : BG.kept_ok 80 PawvY1b.regs0 PawvY1b.regs_out0 KS_awvY1b_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_awvY1b_1 : list nat := Eval vm_compute in (BG.kept_list 80 PawvY1b.regs0 PawvY1b.regs_out1).
Lemma KS_awvY1b_1_ok : BG.kept_ok 80 PawvY1b.regs0 PawvY1b.regs_out1 KS_awvY1b_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvY1b_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 37%nat) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 24) = Z_to_bv 64 ((V 50%nat) + 320) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M ((((V 33%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 400) / 8) + 2147450880) 1 ->
  (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 160)) -> 6905856 <= (V 50%nat) <= 140737488354816 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 512 ->
  L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 50%nat) + 504) (V 51%nat) ->
  4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 512 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) ->
  (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 512 <= (V 33%nat)) -> ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) ->
  ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= (((V 33%nat) / 8) + 2147450880)) -> (65536 + 6840320 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) -> (65536 + 6840320 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= 65536) -> (65536 + 6840320 <= (V 51%nat) \/ (V 51%nat) + 1 <= 65536) ->
  L5.u64_at RSEGS M ((V 33%nat) + 400) (V 38%nat) -> 4136 <= (V 38%nat) <= 140737488355328 -> (65536 + 6840320 <= ((V 38%nat) - 40) \/ ((V 38%nat) - 40) + 40 <= 65536) -> aligned (V 38%nat) 8 ->
  L5.u64_at RSEGS M ((V 38%nat) - 24) (V 39%nat) -> (2147446784 + 17592186048512 <= ((V 38%nat) - 40) \/ ((V 38%nat) - 40) + 40 <= 2147446784) -> L5KA.zeros_at M ((((V 38%nat) - 24) / 8) + 2147450880) 1 -> (((V 2%nat) - 160) + 160 <= ((V 38%nat) - 40) \/ ((V 38%nat) - 40) + 40 <= ((V 2%nat) - 160)) ->
  (((V 38%nat) - 40) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 38%nat) - 40)) -> (((V 38%nat) - 40) + 40 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 38%nat) - 40)) -> (((V 38%nat) - 40) + 40 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 38%nat) - 40)) -> (((((V 38%nat) - 24) / 8) + 2147450880) + 1 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= ((((V 38%nat) - 24) / 8) + 2147450880)) ->
  L5.writable RSEGS M ((V 38%nat) - 24) 8 -> 0 <= (V 37%nat) <= 4 -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((V 33%nat) + 16) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 38%nat) - 24) <= bv_unsigned a < ((V 38%nat) - 24) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 38%nat) - 24) <= i < ((V 38%nat) - 24) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb08c4 M) (st fx' R' 0xb0924 M')
        /\ (forall x, In x KS_awvY1b_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 38%nat) - 24)
        /\ bv_unsigned (getr R' (reg 12)) = (((V 37%nat) + (V 39%nat)) mod 2 ^ 64)
        /\ getr R' (reg 13) = Z_to_bv 64 4
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 400)
        /\ getr R' (reg 25) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880)
        /\ (((V 37%nat) - 4) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 38%nat) - 24) (((V 37%nat) + (V 39%nat)) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xb08c4 M) (st fx' R' 0xae848 M')
        /\ (forall x, In x KS_awvY1b_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 726568
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ bv_unsigned (getr R' (reg 12)) = (((V 37%nat) + (V 39%nat)) mod 2 ^ 64)
        /\ getr R' (reg 13) = Z_to_bv 64 4
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 400)
        /\ getr R' (reg 25) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880)
        /\ 1 <= (((V 37%nat) - 4) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 38%nat) - 24) (((V 37%nat) + (V 39%nat)) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G8 G9 G10 G18 G19 G20 G21 G22 G24 G26 G27 K0 K1 K2 pvzI10 K4 K5 pvzI11 K7 K8 K9 K10 K11 K12 pvzI12 K14 K15 K16 K17 K18 K19 pvzI13 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 pvzI14 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 pvzI15 K46.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV39l; move HV39l before pvzI7; pose proof (proj2 pvzI7) as HV39r; move HV39r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV50l; move HV50l before pvzI8; pose proof (proj2 pvzI8) as HV50r; move HV50r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV51l; move HV51l before pvzI9; pose proof (proj2 pvzI9) as HV51r; move HV51r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K6l; move K6l before pvzI11; pose proof (proj2 pvzI11) as K6r; move K6r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K13l; move K13l before pvzI12; pose proof (proj2 pvzI12) as K13r; move K13r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K20l; move K20l before pvzI13; pose proof (proj2 pvzI13) as K20r; move K20r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K33l; move K33l before pvzI14; pose proof (proj2 pvzI14) as K33r; move K33r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K45l; move K45l before pvzI15; pose proof (proj2 pvzI15) as K45r; move K45r before pvzI15; clear pvzI15.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PawvY1b.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvY1b.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvY1b.kn0).
  { unfold know_ok, PawvY1b.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K39) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K39) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K39) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K24 K25 K39; lia | clear - HV2l HV2r K3l K3r K12 K24 K25 K39; lia | clear - HV2l HV2r K3l K3r K12 K24 K25 K39; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43) | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K42) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K42) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K42) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K42; lia | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K42; lia | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K42; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K42) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K42) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K42) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K42) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K42) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40) | evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | clear; lia | exact K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | evalEk ZA ltac:(clear - HV39l HV39r) | clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43; lia | clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43; lia | clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43; lia | clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43) | evalEk ZA ltac:(clear) | generalize K41; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K42) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43) | evalEk ZA ltac:(clear) | generalize K43; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43; lia | clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43; lia | clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K45l K45r) | exact (conj K45l K45r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K39) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40) | clear - HV2l HV2r K3l K3r K12 K24 K25 K39; lia | clear - HV2l HV2r K3l K3r K12 K24 K25 K39; lia | exactA K46]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvY1b.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvY1b.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_38 - 24) <= bv_unsigned a < (vz_38 - 24) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PawvY1b.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | evalEk' ZA Hag ltac:(clear) | clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PawvY1b.ps0) with 0xb0924 in Hms. change (SR.ps_regs PawvY1b.ps0) with (map (fun i => (i, nth i PawvY1b.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PawvY1b.ps0) with PawvY1b.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvY1b.regs0 PawvY1b.regs_out0 80 KS_awvY1b_0 KS_awvY1b_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PawvY1b.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvY1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PawvY1b.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PawvY1b.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PawvY1b.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PawvY1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PawvY1b.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PawvY1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PawvY1b.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PawvY1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. 
  - right.
    change (SR.ps_pc PawvY1b.ps1) with 0xae848 in Hms. change (SR.ps_regs PawvY1b.ps1) with (map (fun i => (i, nth i PawvY1b.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PawvY1b.ps1) with PawvY1b.cells1 in Hcells. unfold PawvY1b.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvY1b.regs0 PawvY1b.regs_out1 80 KS_awvY1b_1 KS_awvY1b_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PawvY1b.regs_out1 E' R' 1 Hregs) by (clear; lia). cbn [nth PawvY1b.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PawvY1b.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvY1b.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PawvY1b.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvY1b.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PawvY1b.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PawvY1b.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PawvY1b.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PawvY1b.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PawvY1b.regs_out1 E' R' 23 Hregs) by (clear; lia). cbn [nth PawvY1b.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PawvY1b.regs_out1 E' R' 25 Hregs) by (clear; lia). cbn [nth PawvY1b.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvY1c := LibSegBa_awvY1c_b.
Definition KS_awvY1c : list nat := Eval vm_compute in (BG.kept_list 80 PawvY1c.regs0 PawvY1c.regs_out0).
Lemma KS_awvY1c_ok : BG.kept_ok 80 PawvY1c.regs0 PawvY1c.regs_out0 KS_awvY1c = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvY1c_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 25) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M ((((V 33%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 400) / 8) + 2147450880) 1 ->
  (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 160)) -> 6905856 <= (V 50%nat) <= 140737488354816 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 512 ->
  L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 50%nat) + 504) (V 51%nat) ->
  4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 512 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) ->
  (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 512 <= (V 33%nat)) -> ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) ->
  ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= (((V 33%nat) / 8) + 2147450880)) -> (65536 + 6840320 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) -> (65536 + 6840320 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= 65536) -> (65536 + 6840320 <= (V 51%nat) \/ (V 51%nat) + 1 <= 65536) ->
  L5.writable RSEGS M ((V 33%nat) + 8) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 64) -> ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 64) -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1628 M) (st fx' R' 0x7b90c M')
        /\ (forall x, In x KS_awvY1c -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 726080
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880)
        /\ getr R' (reg 11) = Z_to_bv 64 64
        /\ L5.u64_at RSEGS M' (V 50%nat) 1172321806
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450920) 248
        /\ L5.u8_at RSEGS M' ((V 33%nat) + 8) 0
        /\ L5.defined M' ((V 50%nat) + 8) 504).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G18 G19 G20 G21 G22 G23 G25 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 pvzI9 K14 K15 K16 K17 K18 K19 pvzI10 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K13l; move K13l before pvzI9; pose proof (proj2 pvzI9) as K13r; move K13r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K20l; move K20l before pvzI10; pose proof (proj2 pvzI10) as K20r; move K20r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PawvY1c.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvY1c.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvY1c.kn0).
  { unfold know_ok, PawvY1c.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K24 K25; lia | clear - HV2l HV2r K3l K3r K12 K24 K25; lia | clear - HV2l HV2r K3l K3r K12 K24 K25; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31; lia | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31; lia | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | exactA K32]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvY1c.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvY1c.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 8) -> ~ ((((vz_50 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 0) + 64) -> ~ ((vz_33 + 8) <= bv_unsigned a < (vz_33 + 8) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PawvY1c.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvY1c.ps0) with 0x7b90c in Hms. change (SR.ps_regs PawvY1c.ps0) with (map (fun i => (i, nth i PawvY1c.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvY1c.ps0) with PawvY1c.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvY1c.regs0 PawvY1c.regs_out0 80 KS_awvY1c KS_awvY1c_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvY1c.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PawvY1c.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvY1c.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvY1c.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvY1c.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvY1c.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvY2 := LibSegBa_awvY2_b.
Definition KS_awvY2_0 : list nat := Eval vm_compute in (BG.kept_list 80 PawvY2.regs0 PawvY2.regs_out0).
Lemma KS_awvY2_0_ok : BG.kept_ok 80 PawvY2.regs0 PawvY2.regs_out0 KS_awvY2_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_awvY2_1 : list nat := Eval vm_compute in (BG.kept_list 80 PawvY2.regs0 PawvY2.regs_out1).
Lemma KS_awvY2_1_ok : BG.kept_ok 80 PawvY2.regs0 PawvY2.regs_out1 KS_awvY2_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvY2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 24) = Z_to_bv 64 ((V 50%nat) + 320) -> getr R (reg 25) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  140735332487392 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 -> 6905856 <= (V 50%nat) <= 140737488354816 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 512 ->
  L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 50%nat) + 504) (V 51%nat) ->
  4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 512 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) ->
  (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> (65536 + 6840320 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) -> (65536 + 6840320 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= 65536) ->
  (65536 + 6840320 <= (V 51%nat) \/ (V 51%nat) + 1 <= 65536) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((V 33%nat) + 16) -> L5.u32_at RSEGS M ((V 50%nat) + 320) (V 42%nat) -> 0 <= (V 42%nat) <= 4294967295 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb0924 M) (st fx' R' 0xb092c M')
        /\ (forall x, In x KS_awvY2_0 -> getr R' (reg x) = getr R (reg x)))
      \/ (msteps RSEGS (st fx R 0xb0924 M) (st fx' R' 0xae848 M')
        /\ (forall x, In x KS_awvY2_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 726852
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 6)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 pvzI8 K1 K2 pvzI9 K4 pvzI10 K6 K7 K8 K9 K10 K11 pvzI11 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 pvzI12.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV42l; move HV42l before pvzI5; pose proof (proj2 pvzI5) as HV42r; move HV42r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV50l; move HV50l before pvzI6; pose proof (proj2 pvzI6) as HV50r; move HV50r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV51l; move HV51l before pvzI7; pose proof (proj2 pvzI7) as HV51r; move HV51r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K5l; move K5l before pvzI10; pose proof (proj2 pvzI10) as K5r; move K5r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K12l; move K12l before pvzI11; pose proof (proj2 pvzI11) as K12r; move K12r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K23l; move K23l before pvzI12; pose proof (proj2 pvzI12) as K23r; move K23r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 42%nat => Z_to_bv 64 vz_42 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 42%nat => vz_42 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PawvY2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvY2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvY2.kn0).
  { unfold know_ok, PawvY2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K17) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K17) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K17) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K17; lia | clear - HV2l HV2r K0l K0r K16 K17; lia | clear - HV2l HV2r K0l K0r K16 K17; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | clear; lia | exact K6]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19; lia | clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19; lia | clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19; lia | clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19; lia | clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19; lia | clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19; lia | clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk ZA ltac:(clear - HV51l HV51r K12l K12r K14 K15 K17 K20) | clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19; lia | clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K12l K12r K14 K15 K17 K20) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K12l K12r K14 K15 K17 K20) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K12l K12r K14 K15 K17 K20; lia | clear - HV51l HV51r K12l K12r K14 K15 K17 K20; lia | clear - HV51l HV51r K12l K12r K14 K15 K17 K20; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K12l K12r K14 K15 K17 K20) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K12l K12r K14 K15 K17 K20) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K12l K12r K14 K15 K17 K20) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K12l K12r K14 K15 K17 K20) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K17) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r) | clear - HV2l HV2r K0l K0r K16 K17; lia | clear - HV2l HV2r K0l K0r K16 K17; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk ZA ltac:(clear - HV42l HV42r K23l K23r) | clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19; lia | clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvY2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvY2.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PawvY2.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PawvY2.ps0) with 0xb092c in Hms. change (SR.ps_regs PawvY2.ps0) with (map (fun i => (i, nth i PawvY2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PawvY2.ps0) with PawvY2.cells0 in Hcells.
    split. { exact Hms. }
    intros j Hj. apply (BG.kept_regs E E' R R' PawvY2.regs0 PawvY2.regs_out0 80 KS_awvY2_0 KS_awvY2_0_ok HR Hag Hregs j Hj). 
  - right.
    change (SR.ps_pc PawvY2.ps1) with 0xae848 in Hms. change (SR.ps_regs PawvY2.ps1) with (map (fun i => (i, nth i PawvY2.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PawvY2.ps1) with PawvY2.cells1 in Hcells. unfold PawvY2.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvY2.regs0 PawvY2.regs_out1 80 KS_awvY2_1 KS_awvY2_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PawvY2.regs_out1 E' R' 1 Hregs) by (clear; lia). cbn [nth PawvY2.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PawvY2.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvY2.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PawvY2.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvY2.regs_out1]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvY2c := LibSegBa_awvY2c_b.
Definition KS_awvY2c : list nat := Eval vm_compute in (BG.kept_list 80 PawvY2c.regs0 PawvY2c.regs_out0).
Lemma KS_awvY2c_ok : BG.kept_ok 80 PawvY2c.regs0 PawvY2c.regs_out0 KS_awvY2c = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvY2c_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 25) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M ((((V 33%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 400) / 8) + 2147450880) 1 ->
  (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 160)) -> 6905856 <= (V 50%nat) <= 140737488354816 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 512 ->
  L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 50%nat) + 504) (V 51%nat) ->
  4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 512 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) ->
  (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 512 <= (V 33%nat)) -> ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) ->
  ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= (((V 33%nat) / 8) + 2147450880)) -> (65536 + 6840320 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) -> (65536 + 6840320 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= 65536) -> (65536 + 6840320 <= (V 51%nat) \/ (V 51%nat) + 1 <= 65536) ->
  L5.writable RSEGS M ((V 33%nat) + 8) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 64) -> ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 64) -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1744 M) (st fx' R' 0x7b90c M')
        /\ (forall x, In x KS_awvY2c -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 726080
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880)
        /\ getr R' (reg 11) = Z_to_bv 64 64
        /\ L5.u64_at RSEGS M' (V 50%nat) 1172321806
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450920) 248
        /\ L5.u8_at RSEGS M' ((V 33%nat) + 8) 0
        /\ L5.defined M' ((V 50%nat) + 8) 504).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G18 G19 G20 G21 G22 G23 G25 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 pvzI9 K14 K15 K16 K17 K18 K19 pvzI10 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K13l; move K13l before pvzI9; pose proof (proj2 pvzI9) as K13r; move K13r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K20l; move K20l before pvzI10; pose proof (proj2 pvzI10) as K20r; move K20r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PawvY2c.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvY2c.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvY2c.kn0).
  { unfold know_ok, PawvY2c.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K24 K25; lia | clear - HV2l HV2r K3l K3r K12 K24 K25; lia | clear - HV2l HV2r K3l K3r K12 K24 K25; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31; lia | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31; lia | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | exactA K32]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvY2c.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvY2c.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 8) -> ~ ((((vz_50 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 0) + 64) -> ~ ((vz_33 + 8) <= bv_unsigned a < (vz_33 + 8) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PawvY2c.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvY2c.ps0) with 0x7b90c in Hms. change (SR.ps_regs PawvY2c.ps0) with (map (fun i => (i, nth i PawvY2c.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvY2c.ps0) with PawvY2c.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvY2c.regs0 PawvY2c.regs_out0 80 KS_awvY2c KS_awvY2c_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvY2c.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PawvY2c.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvY2c.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvY2c.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvY2c.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvY2c.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvY3a := LibSegBa_awvY3a_b.
Definition KS_awvY3a : list nat := Eval vm_compute in (BG.kept_list 80 PawvY3a.regs0 PawvY3a.regs_out0).
Lemma KS_awvY3a_ok : BG.kept_ok 80 PawvY3a.regs0 PawvY3a.regs_out0 KS_awvY3a = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvY3a_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 24) = Z_to_bv 64 (V 48%nat) -> getr R (reg 25) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) ((V 33%nat) + 16) -> 140735332487392 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 ->
  6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 -> 6905856 <= (V 50%nat) <= 140737488354816 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 512 -> L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 64 ->
  L5.u64_at RSEGS M ((V 50%nat) + 504) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 512 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> (65536 + 6840320 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) ->
  (65536 + 6840320 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= 65536) -> (65536 + 6840320 <= (V 51%nat) \/ (V 51%nat) + 1 <= 65536) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 144) <= bv_unsigned a < ((V 2%nat) - 144) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 42) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 42) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 144) <= i < ((V 2%nat) - 144) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 42) <= i < ((((V 50%nat) / 8) + 2147450880) + 42) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb092c M) (st fx' R' 0xaed4c M')
        /\ (forall x, In x KS_awvY3a -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 723272
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 50%nat) + 336)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) ((V 50%nat) + 336)
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450922) 1).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 pvzI8 K2 K3 pvzI9 K5 pvzI10 K7 K8 K9 K10 K11 K12 pvzI11 K14 K15 K16 K17 K18 K19 K20 K21.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV48l; move HV48l before pvzI5; pose proof (proj2 pvzI5) as HV48r; move HV48r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV50l; move HV50l before pvzI6; pose proof (proj2 pvzI6) as HV50r; move HV50r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV51l; move HV51l before pvzI7; pose proof (proj2 pvzI7) as HV51r; move HV51r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K1l; move K1l before pvzI8; pose proof (proj2 pvzI8) as K1r; move K1r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K4l; move K4l before pvzI9; pose proof (proj2 pvzI9) as K4r; move K4r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K13l; move K13l before pvzI11; pose proof (proj2 pvzI11) as K13r; move K13r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 48%nat => Z_to_bv 64 vz_48 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 48%nat => vz_48 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PawvY3a.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvY3a.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvY3a.kn0).
  { unfold know_ok, PawvY3a.kn0.
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K1l K1r K17 K18) | evalEk ZA ltac:(clear - HV33l HV33r K4l K4r) | clear - HV2l HV2r K1l K1r K17 K18; lia | clear - HV2l HV2r K1l K1r K17 K18; lia | exactA K0]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K1l K1r K17 K18) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K1l K1r K17 K18) | clear; lia | exact K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K1l K1r K17 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K1l K1r K17 K18; lia | clear - HV2l HV2r K1l K1r K17 K18; lia | clear - HV2l HV2r K1l K1r K17 K18; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K4l K4r) | clear; lia | exact K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K6l K6r K10 K16 K17 K19 K20) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K6l K6r K10 K16 K17 K19 K20) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K6l K6r K10 K16 K17 K19 K20) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K6l K6r K10 K16 K17 K19 K20; lia | clear - HV50l HV50r K6l K6r K10 K16 K17 K19 K20; lia | clear - HV50l HV50r K6l K6r K10 K16 K17 K19 K20; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K6l K6r K10 K16 K17 K19 K20) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K6l K6r K10 K16 K17 K19 K20; lia | clear - HV50l HV50r K6l K6r K10 K16 K17 K19 K20; lia | clear - HV50l HV50r K6l K6r K10 K16 K17 K19 K20; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K6l K6r K10 K16 K17 K19 K20) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K6l K6r K10 K16 K17 K19 K20) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K6l K6r K10 K16 K17 K19 K20; lia | clear - HV50l HV50r K6l K6r K10 K16 K17 K19 K20; lia | clear - HV50l HV50r K6l K6r K10 K16 K17 K19 K20; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K6l K6r K10 K16 K17 K19 K20) | evalEk ZA ltac:(clear - HV51l HV51r K13l K13r K15 K16 K18 K21) | clear - HV50l HV50r K6l K6r K10 K16 K17 K19 K20; lia | clear - HV50l HV50r K6l K6r K10 K16 K17 K19 K20; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K13l K13r K15 K16 K18 K21) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K13l K13r K15 K16 K18 K21) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K13l K13r K15 K16 K18 K21; lia | clear - HV51l HV51r K13l K13r K15 K16 K18 K21; lia | clear - HV51l HV51r K13l K13r K15 K16 K18 K21; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K13l K13r K15 K16 K18 K21) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K6l K6r K10 K16 K17 K19 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K13l K13r K15 K16 K18 K21) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K1l K1r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K6l K6r K10 K16 K17 K19 K20) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K1l K1r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K13l K13r K15 K16 K18 K21) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K6l K6r K10 K16 K17 K19 K20) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K6l K6r K10 K16 K17 K19 K20) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K13l K13r K15 K16 K18 K21) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvY3a.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvY3a.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 144) <= bv_unsigned a < (vz_2 - 144) + 8) -> ~ ((((vz_50 / 8) + 2147450880) + 42) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 42) + 1) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PawvY3a.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K1l K1r K17 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K1l K1r K17 K18 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K6l K6r K10 K16 K17 K19 K20) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K6l K6r K10 K16 K17 K19 K20 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvY3a.ps0) with 0xaed4c in Hms. change (SR.ps_regs PawvY3a.ps0) with (map (fun i => (i, nth i PawvY3a.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvY3a.ps0) with PawvY3a.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvY3a.regs0 PawvY3a.regs_out0 80 KS_awvY3a KS_awvY3a_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvY3a.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PawvY3a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvY3a.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvY3a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvY3a.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvY3a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvY3a.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PawvY3a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K1l K1r K17 K18) | evalEk' ZA Hag ltac:(clear - HV50l HV50r K6l K6r K10 K16 K17 K19 K20) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K6l K6r K10 K16 K17 K19 K20) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvY3b := LibSegBa_awvY3b_b.
Definition KS_awvY3b_0 : list nat := Eval vm_compute in (BG.kept_list 80 PawvY3b.regs0 PawvY3b.regs_out0).
Lemma KS_awvY3b_0_ok : BG.kept_ok 80 PawvY3b.regs0 PawvY3b.regs_out0 KS_awvY3b_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_awvY3b_1 : list nat := Eval vm_compute in (BG.kept_list 80 PawvY3b.regs0 PawvY3b.regs_out1).
Lemma KS_awvY3b_1_ok : BG.kept_ok 80 PawvY3b.regs0 PawvY3b.regs_out1 KS_awvY3b_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvY3b_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 37%nat) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 24) = Z_to_bv 64 (V 48%nat) -> getr R (reg 25) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M ((((V 33%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 400) / 8) + 2147450880) 1 ->
  (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 160)) -> 6905856 <= (V 50%nat) <= 140737488354816 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 512 ->
  L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 50%nat) + 504) (V 51%nat) ->
  4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 512 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) ->
  (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 512 <= (V 33%nat)) -> ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) ->
  ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= (((V 33%nat) / 8) + 2147450880)) -> (65536 + 6840320 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) -> (65536 + 6840320 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= 65536) -> (65536 + 6840320 <= (V 51%nat) \/ (V 51%nat) + 1 <= 65536) ->
  L5.u64_at RSEGS M ((V 33%nat) + 400) (V 38%nat) -> 4136 <= (V 38%nat) <= 140737488355328 -> (65536 + 6840320 <= ((V 38%nat) - 40) \/ ((V 38%nat) - 40) + 40 <= 65536) -> aligned (V 38%nat) 8 ->
  L5.u64_at RSEGS M ((V 38%nat) - 24) (V 39%nat) -> (2147446784 + 17592186048512 <= ((V 38%nat) - 40) \/ ((V 38%nat) - 40) + 40 <= 2147446784) -> L5KA.zeros_at M ((((V 38%nat) - 24) / 8) + 2147450880) 1 -> (((V 2%nat) - 160) + 160 <= ((V 38%nat) - 40) \/ ((V 38%nat) - 40) + 40 <= ((V 2%nat) - 160)) ->
  (((V 38%nat) - 40) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 38%nat) - 40)) -> (((V 38%nat) - 40) + 40 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 38%nat) - 40)) -> (((V 38%nat) - 40) + 40 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 38%nat) - 40)) -> (((((V 38%nat) - 24) / 8) + 2147450880) + 1 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= ((((V 38%nat) - 24) / 8) + 2147450880)) ->
  L5.writable RSEGS M ((V 38%nat) - 24) 8 -> 0 <= (V 37%nat) <= 1 -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((V 33%nat) + 16) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 38%nat) - 24) <= bv_unsigned a < ((V 38%nat) - 24) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 38%nat) - 24) <= i < ((V 38%nat) - 24) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb0948 M) (st fx' R' 0xb099c M')
        /\ (forall x, In x KS_awvY3b_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 38%nat) - 24)
        /\ bv_unsigned (getr R' (reg 12)) = (((V 37%nat) + (V 39%nat)) mod 2 ^ 64)
        /\ getr R' (reg 13) = Z_to_bv 64 1
        /\ (((V 37%nat) - 1) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 38%nat) - 24) (((V 37%nat) + (V 39%nat)) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xb0948 M) (st fx' R' 0xae848 M')
        /\ (forall x, In x KS_awvY3b_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 726892
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ bv_unsigned (getr R' (reg 12)) = (((V 37%nat) + (V 39%nat)) mod 2 ^ 64)
        /\ getr R' (reg 13) = Z_to_bv 64 1
        /\ 1 <= (((V 37%nat) - 1) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 38%nat) - 24) (((V 37%nat) + (V 39%nat)) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI11 K4 K5 pvzI12 K7 K8 K9 K10 K11 K12 pvzI13 K14 K15 K16 K17 K18 K19 pvzI14 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 pvzI15 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 pvzI16 K46.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV39l; move HV39l before pvzI7; pose proof (proj2 pvzI7) as HV39r; move HV39r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV48l; move HV48l before pvzI8; pose proof (proj2 pvzI8) as HV48r; move HV48r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV50l; move HV50l before pvzI9; pose proof (proj2 pvzI9) as HV50r; move HV50r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV51l; move HV51l before pvzI10; pose proof (proj2 pvzI10) as HV51r; move HV51r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K3l; move K3l before pvzI11; pose proof (proj2 pvzI11) as K3r; move K3r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K6l; move K6l before pvzI12; pose proof (proj2 pvzI12) as K6r; move K6r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K13l; move K13l before pvzI13; pose proof (proj2 pvzI13) as K13r; move K13r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K20l; move K20l before pvzI14; pose proof (proj2 pvzI14) as K20r; move K20r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K33l; move K33l before pvzI15; pose proof (proj2 pvzI15) as K33r; move K33r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K45l; move K45l before pvzI16; pose proof (proj2 pvzI16) as K45r; move K45r before pvzI16; clear pvzI16.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 48%nat => Z_to_bv 64 vz_48 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 48%nat => vz_48 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PawvY3b.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvY3b.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvY3b.kn0).
  { unfold know_ok, PawvY3b.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K39) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K39) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K39) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K24 K25 K39; lia | clear - HV2l HV2r K3l K3r K12 K24 K25 K39; lia | clear - HV2l HV2r K3l K3r K12 K24 K25 K39; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43) | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K42) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K42) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K42) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K42; lia | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K42; lia | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K42; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K42) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K42) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K42) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K42) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K42) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40) | evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | clear; lia | exact K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | evalEk ZA ltac:(clear - HV39l HV39r) | clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43; lia | clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43; lia | clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43; lia | clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43) | evalEk ZA ltac:(clear) | generalize K41; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K42) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43) | evalEk ZA ltac:(clear) | generalize K43; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43; lia | clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43; lia | clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K45l K45r) | exact (conj K45l K45r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K39) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40) | clear - HV2l HV2r K3l K3r K12 K24 K25 K39; lia | clear - HV2l HV2r K3l K3r K12 K24 K25 K39; lia | exactA K46]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvY3b.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvY3b.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_38 - 24) <= bv_unsigned a < (vz_38 - 24) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PawvY3b.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | evalEk' ZA Hag ltac:(clear) | clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PawvY3b.ps0) with 0xb099c in Hms. change (SR.ps_regs PawvY3b.ps0) with (map (fun i => (i, nth i PawvY3b.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PawvY3b.ps0) with PawvY3b.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvY3b.regs0 PawvY3b.regs_out0 80 KS_awvY3b_0 KS_awvY3b_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PawvY3b.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvY3b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PawvY3b.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PawvY3b.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PawvY3b.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PawvY3b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. 
  - right.
    change (SR.ps_pc PawvY3b.ps1) with 0xae848 in Hms. change (SR.ps_regs PawvY3b.ps1) with (map (fun i => (i, nth i PawvY3b.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PawvY3b.ps1) with PawvY3b.cells1 in Hcells. unfold PawvY3b.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvY3b.regs0 PawvY3b.regs_out1 80 KS_awvY3b_1 KS_awvY3b_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PawvY3b.regs_out1 E' R' 1 Hregs) by (clear; lia). cbn [nth PawvY3b.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PawvY3b.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvY3b.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PawvY3b.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvY3b.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PawvY3b.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PawvY3b.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PawvY3b.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PawvY3b.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvY3c := LibSegBa_awvY3c_b.
Definition KS_awvY3c : list nat := Eval vm_compute in (BG.kept_list 80 PawvY3c.regs0 PawvY3c.regs_out0).
Lemma KS_awvY3c_ok : BG.kept_ok 80 PawvY3c.regs0 PawvY3c.regs_out0 KS_awvY3c = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvY3c_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 25) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M ((((V 33%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 400) / 8) + 2147450880) 1 ->
  (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 160)) -> 6905856 <= (V 50%nat) <= 140737488354816 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 512 ->
  L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 50%nat) + 504) (V 51%nat) ->
  4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 512 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) ->
  (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 512 <= (V 33%nat)) -> ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) ->
  ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= (((V 33%nat) / 8) + 2147450880)) -> (65536 + 6840320 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) -> (65536 + 6840320 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= 65536) -> (65536 + 6840320 <= (V 51%nat) \/ (V 51%nat) + 1 <= 65536) ->
  L5.writable RSEGS M ((V 33%nat) + 8) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 64) -> ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 64) -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb176c M) (st fx' R' 0x7b90c M')
        /\ (forall x, In x KS_awvY3c -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 726080
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880)
        /\ getr R' (reg 11) = Z_to_bv 64 64
        /\ L5.u64_at RSEGS M' (V 50%nat) 1172321806
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450920) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450922) 248
        /\ L5.u8_at RSEGS M' ((V 33%nat) + 8) 0
        /\ L5.defined M' ((V 50%nat) + 8) 504).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G18 G19 G20 G21 G22 G23 G25 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 pvzI9 K14 K15 K16 K17 K18 K19 pvzI10 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K13l; move K13l before pvzI9; pose proof (proj2 pvzI9) as K13r; move K13r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K20l; move K20l before pvzI10; pose proof (proj2 pvzI10) as K20r; move K20r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PawvY3c.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvY3c.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvY3c.kn0).
  { unfold know_ok, PawvY3c.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K24 K25; lia | clear - HV2l HV2r K3l K3r K12 K24 K25; lia | clear - HV2l HV2r K3l K3r K12 K24 K25; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31; lia | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31; lia | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | exactA K32]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvY3c.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvY3c.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 8) -> ~ ((((vz_50 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 0) + 64) -> ~ ((vz_33 + 8) <= bv_unsigned a < (vz_33 + 8) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PawvY3c.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvY3c.ps0) with 0x7b90c in Hms. change (SR.ps_regs PawvY3c.ps0) with (map (fun i => (i, nth i PawvY3c.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvY3c.ps0) with PawvY3c.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvY3c.regs0 PawvY3c.regs_out0 80 KS_awvY3c KS_awvY3c_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvY3c.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PawvY3c.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvY3c.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvY3c.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvY3c.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvY3c.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvY4a := LibSegBa_awvY4a_b.
Definition KS_awvY4a : list nat := Eval vm_compute in (BG.kept_list 80 PawvY4a.regs0 PawvY4a.regs_out0).
Lemma KS_awvY4a_ok : BG.kept_ok 80 PawvY4a.regs0 PawvY4a.regs_out0 KS_awvY4a = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvY4a_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 24) = Z_to_bv 64 (V 48%nat) -> getr R (reg 25) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) ((V 33%nat) + 16) -> 140735332487392 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 ->
  6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb099c M) (st fx' R' 0xb3bfc M')
        /\ (forall x, In x KS_awvY4a -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 723372
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + 320)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 pvzI7 K2 K3 pvzI8 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV48l; move HV48l before pvzI5; pose proof (proj2 pvzI5) as HV48r; move HV48r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV50l; move HV50l before pvzI6; pose proof (proj2 pvzI6) as HV50r; move HV50r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K1l; move K1l before pvzI7; pose proof (proj2 pvzI7) as K1r; move K1r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 48%nat => Z_to_bv 64 vz_48 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 48%nat => vz_48 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PawvY4a.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvY4a.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvY4a.kn0).
  { unfold know_ok, PawvY4a.kn0.
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K1l K1r) | evalEk ZA ltac:(clear - HV33l HV33r K4l K4r) | clear - HV2l HV2r K1l K1r; lia | clear - HV2l HV2r K1l K1r; lia | exactA K0]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K1l K1r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K1l K1r) | clear; lia | exact K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K1l K1r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K1l K1r; lia | clear - HV2l HV2r K1l K1r; lia | clear - HV2l HV2r K1l K1r; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K4l K4r) | clear; lia | exact K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvY4a.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvY4a.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PawvY4a.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvY4a.ps0) with 0xb3bfc in Hms. change (SR.ps_regs PawvY4a.ps0) with (map (fun i => (i, nth i PawvY4a.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvY4a.ps0) with PawvY4a.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvY4a.regs0 PawvY4a.regs_out0 80 KS_awvY4a KS_awvY4a_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvY4a.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PawvY4a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvY4a.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvY4a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvY4a.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvY4a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PawvY4a.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PawvY4a.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvY4b := LibSegBa_awvY4b_b.
Definition KS_awvY4b_0 : list nat := Eval vm_compute in (BG.kept_list 80 PawvY4b.regs0 PawvY4b.regs_out0).
Lemma KS_awvY4b_0_ok : BG.kept_ok 80 PawvY4b.regs0 PawvY4b.regs_out0 KS_awvY4b_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_awvY4b_1 : list nat := Eval vm_compute in (BG.kept_list 80 PawvY4b.regs0 PawvY4b.regs_out1).
Lemma KS_awvY4b_1_ok : BG.kept_ok 80 PawvY4b.regs0 PawvY4b.regs_out1 KS_awvY4b_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvY4b_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 45%nat) -> getr R (reg 11) = Z_to_bv 64 (V 46%nat) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 24) = Z_to_bv 64 (V 48%nat) -> getr R (reg 25) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  140735332487392 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((V 33%nat) + 16) -> 0 <= (V 48%nat) <= 2147483647 -> 0 <= (V 46%nat) <= 2147483647 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb09ac M) (st fx' R' 0xb09b0 M')
        /\ (forall x, In x KS_awvY4b_0 -> getr R' (reg x) = getr R (reg x))
        /\ (((V 46%nat) - (V 48%nat)) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0xb09ac M) (st fx' R' 0xae848 M')
        /\ (forall x, In x KS_awvY4b_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 726936
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ 1 <= (((V 46%nat) - (V 48%nat)) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G10 G11 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 pvzI9 K1 K2 pvzI10 K4 K5 pvzI11 pvzI12.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV45l; move HV45l before pvzI5; pose proof (proj2 pvzI5) as HV45r; move HV45r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV46l; move HV46l before pvzI6; pose proof (proj2 pvzI6) as HV46r; move HV46r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV48l; move HV48l before pvzI7; pose proof (proj2 pvzI7) as HV48r; move HV48r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV50l; move HV50l before pvzI8; pose proof (proj2 pvzI8) as HV50r; move HV50r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K0l; move K0l before pvzI9; pose proof (proj2 pvzI9) as K0r; move K0r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K6l; move K6l before pvzI11; pose proof (proj2 pvzI11) as K6r; move K6r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K7l; move K7l before pvzI12; pose proof (proj2 pvzI12) as K7r; move K7r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 48%nat => Z_to_bv 64 vz_48 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 45%nat => vz_45 | 46%nat => vz_46 | 48%nat => vz_48 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PawvY4b.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvY4b.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvY4b.kn0).
  { unfold know_ok, PawvY4b.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvY4b.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvY4b.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PawvY4b.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PawvY4b.ps0) with 0xb09b0 in Hms. change (SR.ps_regs PawvY4b.ps0) with (map (fun i => (i, nth i PawvY4b.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PawvY4b.ps0) with PawvY4b.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvY4b.regs0 PawvY4b.regs_out0 80 KS_awvY4b_0 KS_awvY4b_0_ok HR Hag Hregs j Hj). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  - right.
    change (SR.ps_pc PawvY4b.ps1) with 0xae848 in Hms. change (SR.ps_regs PawvY4b.ps1) with (map (fun i => (i, nth i PawvY4b.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PawvY4b.ps1) with PawvY4b.cells1 in Hcells. unfold PawvY4b.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvY4b.regs0 PawvY4b.regs_out1 80 KS_awvY4b_1 KS_awvY4b_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PawvY4b.regs_out1 E' R' 1 Hregs) by (clear; lia). cbn [nth PawvY4b.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PawvY4b.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvY4b.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PawvY4b.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvY4b.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvY4c := LibSegBa_awvY4c_b.
Definition KS_awvY4c : list nat := Eval vm_compute in (BG.kept_list 80 PawvY4c.regs0 PawvY4c.regs_out0).
Lemma KS_awvY4c_ok : BG.kept_ok 80 PawvY4c.regs0 PawvY4c.regs_out0 KS_awvY4c = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvY4c_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 25) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M ((((V 33%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 400) / 8) + 2147450880) 1 ->
  (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 160)) -> 6905856 <= (V 50%nat) <= 140737488354816 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 512 ->
  L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 50%nat) + 504) (V 51%nat) ->
  4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 512 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) ->
  (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 512 <= (V 33%nat)) -> ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) ->
  ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= (((V 33%nat) / 8) + 2147450880)) -> (65536 + 6840320 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) -> (65536 + 6840320 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= 65536) -> (65536 + 6840320 <= (V 51%nat) \/ (V 51%nat) + 1 <= 65536) ->
  L5.writable RSEGS M ((V 33%nat) + 8) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 64) -> ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 64) -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1798 M) (st fx' R' 0x7b90c M')
        /\ (forall x, In x KS_awvY4c -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 726080
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880)
        /\ getr R' (reg 11) = Z_to_bv 64 64
        /\ L5.u64_at RSEGS M' (V 50%nat) 1172321806
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450920) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450922) 248
        /\ L5.u8_at RSEGS M' ((V 33%nat) + 8) 0
        /\ L5.defined M' ((V 50%nat) + 8) 504).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G18 G19 G20 G21 G22 G23 G25 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 pvzI9 K14 K15 K16 K17 K18 K19 pvzI10 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K13l; move K13l before pvzI9; pose proof (proj2 pvzI9) as K13r; move K13r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K20l; move K20l before pvzI10; pose proof (proj2 pvzI10) as K20r; move K20r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PawvY4c.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvY4c.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvY4c.kn0).
  { unfold know_ok, PawvY4c.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K24 K25; lia | clear - HV2l HV2r K3l K3r K12 K24 K25; lia | clear - HV2l HV2r K3l K3r K12 K24 K25; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31; lia | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31; lia | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | exactA K32]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvY4c.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvY4c.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 8) -> ~ ((((vz_50 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 0) + 64) -> ~ ((vz_33 + 8) <= bv_unsigned a < (vz_33 + 8) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PawvY4c.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvY4c.ps0) with 0x7b90c in Hms. change (SR.ps_regs PawvY4c.ps0) with (map (fun i => (i, nth i PawvY4c.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvY4c.ps0) with PawvY4c.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvY4c.regs0 PawvY4c.regs_out0 80 KS_awvY4c KS_awvY4c_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvY4c.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PawvY4c.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvY4c.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvY4c.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvY4c.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvY4c.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvY5a := LibSegBa_awvY5a_b.
Definition KS_awvY5a : list nat := Eval vm_compute in (BG.kept_list 80 PawvY5a.regs0 PawvY5a.regs_out0).
Lemma KS_awvY5a_ok : BG.kept_ok 80 PawvY5a.regs0 PawvY5a.regs_out0 KS_awvY5a = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvY5a_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 45%nat) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 24) = Z_to_bv 64 (V 48%nat) -> getr R (reg 25) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M ((((V 33%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 400) / 8) + 2147450880) 1 ->
  (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 160)) -> 6905856 <= (V 50%nat) <= 140737488354816 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 512 ->
  L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 50%nat) + 504) (V 51%nat) ->
  4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 512 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) ->
  (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 512 <= (V 33%nat)) -> ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) ->
  ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= (((V 33%nat) / 8) + 2147450880)) -> (65536 + 6840320 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) -> (65536 + 6840320 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= 65536) -> (65536 + 6840320 <= (V 51%nat) \/ (V 51%nat) + 1 <= 65536) ->
  L5.u64_at RSEGS M ((V 33%nat) + 400) (V 38%nat) -> 4136 <= (V 38%nat) <= 140737488355328 -> (65536 + 6840320 <= ((V 38%nat) - 40) \/ ((V 38%nat) - 40) + 40 <= 65536) -> aligned (V 38%nat) 8 ->
  L5.u64_at RSEGS M ((V 38%nat) - 24) (V 39%nat) -> (2147446784 + 17592186048512 <= ((V 38%nat) - 40) \/ ((V 38%nat) - 40) + 40 <= 2147446784) -> L5KA.zeros_at M ((((V 38%nat) - 24) / 8) + 2147450880) 1 -> (((V 2%nat) - 160) + 160 <= ((V 38%nat) - 40) \/ ((V 38%nat) - 40) + 40 <= ((V 2%nat) - 160)) ->
  (((V 38%nat) - 40) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 38%nat) - 40)) -> (((V 38%nat) - 40) + 40 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 38%nat) - 40)) -> (((V 38%nat) - 40) + 40 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 38%nat) - 40)) -> (((((V 38%nat) - 24) / 8) + 2147450880) + 1 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= ((((V 38%nat) - 24) / 8) + 2147450880)) ->
  L5.writable RSEGS M ((V 38%nat) - 24) 8 -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((V 33%nat) + 16) -> 0 <= (V 48%nat) <= 2147483647 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 38%nat) - 24) <= bv_unsigned a < ((V 38%nat) - 24) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 38%nat) - 24) <= i < ((V 38%nat) - 24) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb09b0 M) (st fx' R' 0xb0a00 M')
        /\ (forall x, In x KS_awvY5a -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 50%nat) + 32)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 38%nat) - 24)
        /\ bv_unsigned (getr R' (reg 13)) = (((V 39%nat) + (V 48%nat)) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 38%nat) - 24) (((V 39%nat) + (V 48%nat)) mod 2 ^ 64)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI11 K4 K5 pvzI12 K7 K8 K9 K10 K11 K12 pvzI13 K14 K15 K16 K17 K18 K19 pvzI14 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 pvzI15 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 pvzI16.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV39l; move HV39l before pvzI6; pose proof (proj2 pvzI6) as HV39r; move HV39r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV45l; move HV45l before pvzI7; pose proof (proj2 pvzI7) as HV45r; move HV45r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV48l; move HV48l before pvzI8; pose proof (proj2 pvzI8) as HV48r; move HV48r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV50l; move HV50l before pvzI9; pose proof (proj2 pvzI9) as HV50r; move HV50r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV51l; move HV51l before pvzI10; pose proof (proj2 pvzI10) as HV51r; move HV51r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K3l; move K3l before pvzI11; pose proof (proj2 pvzI11) as K3r; move K3r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K6l; move K6l before pvzI12; pose proof (proj2 pvzI12) as K6r; move K6r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K13l; move K13l before pvzI13; pose proof (proj2 pvzI13) as K13r; move K13r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K20l; move K20l before pvzI14; pose proof (proj2 pvzI14) as K20r; move K20r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K33l; move K33l before pvzI15; pose proof (proj2 pvzI15) as K33r; move K33r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K46l; move K46l before pvzI16; pose proof (proj2 pvzI16) as K46r; move K46r before pvzI16; clear pvzI16.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 45%nat => Z_to_bv 64 vz_45 | 48%nat => Z_to_bv 64 vz_48 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 38%nat => vz_38 | 39%nat => vz_39 | 45%nat => vz_45 | 48%nat => vz_48 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PawvY5a.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvY5a.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvY5a.kn0).
  { unfold know_ok, PawvY5a.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K39) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K39) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K39) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K24 K25 K39; lia | clear - HV2l HV2r K3l K3r K12 K24 K25 K39; lia | clear - HV2l HV2r K3l K3r K12 K24 K25 K39; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43) | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K42) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K42) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K42) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K42; lia | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K42; lia | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K42; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K42) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K42) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K42) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K42) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K42) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40) | evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | clear; lia | exact K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | evalEk ZA ltac:(clear - HV39l HV39r) | clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43; lia | clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43; lia | clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43; lia | clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43) | evalEk ZA ltac:(clear) | generalize K41; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K42) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K41 K43) | evalEk ZA ltac:(clear) | generalize K43; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43; lia | clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43; lia | clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K39) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K40) | clear - HV2l HV2r K3l K3r K12 K24 K25 K39; lia | clear - HV2l HV2r K3l K3r K12 K24 K25 K39; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K46l K46r) | exact (conj K46l K46r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvY5a.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvY5a.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_38 - 24) <= bv_unsigned a < (vz_38 - 24) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PawvY5a.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | evalEk' ZA Hag ltac:(clear) | clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvY5a.ps0) with 0xb0a00 in Hms. change (SR.ps_regs PawvY5a.ps0) with (map (fun i => (i, nth i PawvY5a.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvY5a.ps0) with PawvY5a.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvY5a.regs0 PawvY5a.regs_out0 80 KS_awvY5a KS_awvY5a_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvY5a.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvY5a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvY5a.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PawvY5a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvY5a.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PawvY5a.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvY5b := LibSegBa_awvY5b_b.
Definition KS_awvY5b : list nat := Eval vm_compute in (BG.kept_list 80 PawvY5b.regs0 PawvY5b.regs_out0).
Lemma KS_awvY5b_ok : BG.kept_ok 80 PawvY5b.regs0 PawvY5b.regs_out0 KS_awvY5b = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvY5b_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 45%nat) -> getr R (reg 11) = Z_to_bv 64 ((V 50%nat) + 32) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 24) = Z_to_bv 64 (V 48%nat) -> getr R (reg 25) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487408 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M ((((V 33%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 400) / 8) + 2147450880) 1 ->
  (((V 2%nat) - 176) + 176 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 176)) -> 6905856 <= (V 50%nat) <= 140737488354816 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 512 ->
  L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 50%nat) + 504) (V 51%nat) ->
  4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 512 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) ->
  (((V 2%nat) - 176) + 176 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 176)) -> (((V 2%nat) - 176) + 176 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 176)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 512 <= (V 33%nat)) -> ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) ->
  ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= (((V 33%nat) / 8) + 2147450880)) -> (65536 + 6840320 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) -> (65536 + 6840320 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= 65536) -> (65536 + 6840320 <= (V 51%nat) \/ (V 51%nat) + 1 <= 65536) ->
  6905856 <= (V 34%nat) <= 140737488355320 -> aligned (V 34%nat) 8 -> (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 ->
  (((V 2%nat) - 176) + 176 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 2%nat) - 176)) -> ((V 33%nat) + 416 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 33%nat)) -> ((V 50%nat) + 512 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 50%nat)) -> ((V 51%nat) + 1 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 51%nat)) ->
  L5.u64_at RSEGS M (V 34%nat) 1251456 -> L5KA.zeros_at M 2147607329 1 -> ((((V 34%nat) / 8) + 2147450880) + 1 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= (((V 34%nat) / 8) + 2147450880)) -> L5KA.zeros_at M 2147607328 1 ->
  L5.u64_at RSEGS M ((V 2%nat) - 144) ((V 50%nat) + 336) -> L5.u8_at RSEGS M ((V 50%nat) + 336) (V 43%nat) -> 0 <= (V 43%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 32) <= bv_unsigned a < ((V 50%nat) + 32) + 16) -> ~ (((((V 50%nat) / 8) + 2147450880) + 4) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 4) + 2) -> ~ (((V 2%nat) - 176) <= bv_unsigned a < ((V 2%nat) - 176) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 32) <= i < ((V 50%nat) + 32) + 16) -> ~ (((((V 50%nat) / 8) + 2147450880) + 4) <= i < ((((V 50%nat) / 8) + 2147450880) + 4) + 2) -> ~ (((V 2%nat) - 176) <= i < ((V 2%nat) - 176) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb0a00 M) (st fx' R' 0xb0a5c M')
        /\ (forall x, In x KS_awvY5b -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 723548
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 692924
        /\ getr R' (reg 16) = Z_to_bv 64 156448
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 40) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 32) (V 45%nat)
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450885) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450884) 0
        /\ L5.defined M' (V 50%nat) 32
        /\ L5.defined M' ((V 50%nat) + 48) 464).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G8 G9 G10 G11 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI10 K4 K5 pvzI11 K7 K8 K9 K10 K11 K12 pvzI12 K14 K15 K16 K17 K18 K19 pvzI13 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 pvzI14 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 pvzI15.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV43l; move HV43l before pvzI5; pose proof (proj2 pvzI5) as HV43r; move HV43r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV45l; move HV45l before pvzI6; pose proof (proj2 pvzI6) as HV45r; move HV45r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV48l; move HV48l before pvzI7; pose proof (proj2 pvzI7) as HV48r; move HV48r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV50l; move HV50l before pvzI8; pose proof (proj2 pvzI8) as HV50r; move HV50r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV51l; move HV51l before pvzI9; pose proof (proj2 pvzI9) as HV51r; move HV51r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K6l; move K6l before pvzI11; pose proof (proj2 pvzI11) as K6r; move K6r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K13l; move K13l before pvzI12; pose proof (proj2 pvzI12) as K13r; move K13r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K20l; move K20l before pvzI13; pose proof (proj2 pvzI13) as K20r; move K20r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K32l; move K32l before pvzI14; pose proof (proj2 pvzI14) as K32r; move K32r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K46l; move K46l before pvzI15; pose proof (proj2 pvzI15) as K46r; move K46r before pvzI15; clear pvzI15.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 43%nat => Z_to_bv 64 vz_43 | 45%nat => Z_to_bv 64 vz_45 | 48%nat => Z_to_bv 64 vz_48 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 43%nat => vz_43 | 45%nat => vz_45 | 48%nat => vz_48 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PawvY5b.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvY5b.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvY5b.kn0).
  { unfold know_ok, PawvY5b.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K36) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K36) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K36) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K24 K25 K36; lia | clear - HV2l HV2r K3l K3r K12 K24 K25 K36; lia | clear - HV2l HV2r K3l K3r K12 K24 K25 K36; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39; lia | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39; lia | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K32l K32r K34 K36 K37 K38 K39 K42) | exact (conj K32l K32r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K32l K32r K34 K36 K37 K38 K39 K42) | clear; lia | exact K33]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K32l K32r K34 K36 K37 K38 K39 K42) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K32l K32r K34 K36 K37 K38 K39 K42) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K32l K32r K34 K36 K37 K38 K39 K42; lia | clear - HV34l HV34r K32l K32r K34 K36 K37 K38 K39 K42; lia | clear - HV34l HV34r K32l K32r K34 K36 K37 K38 K39 K42; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K32l K32r K34 K36 K37 K38 K39 K42) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K32l K32r K34 K36 K37 K38 K39 K42) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K32l K32r K34 K36 K37 K38 K39 K42) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K32l K32r K34 K36 K37 K38 K39 K42) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K32l K32r K34 K36 K37 K38 K39 K42) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K32l K32r K34 K36 K37 K38 K39 K42; lia | clear - HV34l HV34r K32l K32r K34 K36 K37 K38 K39 K42; lia | exactA K40]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K32l K32r K34 K36 K37 K38 K39 K42) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K36) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | clear - HV2l HV2r K3l K3r K12 K24 K25 K36; lia | clear - HV2l HV2r K3l K3r K12 K24 K25 K36; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk ZA ltac:(clear - HV43l HV43r K46l K46r) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42; lia | byte_tac ltac:(clear - HV43l HV43r K46l K46r) | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K46l K46r) | exact (conj K46l K46r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvY5b.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvY5b.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_50 + 32) <= bv_unsigned a < (vz_50 + 32) + 16) -> ~ ((((vz_50 / 8) + 2147450880) + 4) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 4) + 2) -> ~ ((vz_2 - 176) <= bv_unsigned a < (vz_2 - 176) + 16) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PawvY5b.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K36) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K24 K25 K36 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvY5b.ps0) with 0xb0a5c in Hms. change (SR.ps_regs PawvY5b.ps0) with (map (fun i => (i, nth i PawvY5b.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvY5b.ps0) with PawvY5b.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvY5b.regs0 PawvY5b.regs_out0 80 KS_awvY5b KS_awvY5b_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvY5b.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PawvY5b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvY5b.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvY5b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvY5b.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PawvY5b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvY5b.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PawvY5b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvY5b.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PawvY5b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvY5b.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PawvY5b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvY5b.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PawvY5b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvY5c := LibSegBa_awvY5c_b.
Definition KS_awvY5c : list nat := Eval vm_compute in (BG.kept_list 80 PawvY5c.regs0 PawvY5c.regs_out0).
Lemma KS_awvY5c_ok : BG.kept_ok 80 PawvY5c.regs0 PawvY5c.regs_out0 KS_awvY5c = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvY5c_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 25) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M ((((V 33%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 400) / 8) + 2147450880) 1 ->
  (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 160)) -> 6905856 <= (V 50%nat) <= 140737488354816 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 512 ->
  L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 50%nat) + 504) (V 51%nat) ->
  4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 512 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) ->
  (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 512 <= (V 33%nat)) -> ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) ->
  ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= (((V 33%nat) / 8) + 2147450880)) -> (65536 + 6840320 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) -> (65536 + 6840320 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= 65536) -> (65536 + 6840320 <= (V 51%nat) \/ (V 51%nat) + 1 <= 65536) ->
  L5.writable RSEGS M ((V 33%nat) + 8) 1 -> L5.u8_at RSEGS M ((V 33%nat) + 10) 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 64) -> ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 64) -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb0a5c M) (st fx' R' 0x7b90c M')
        /\ (forall x, In x KS_awvY5c -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 726080
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880)
        /\ getr R' (reg 11) = Z_to_bv 64 64
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' (V 50%nat) 1172321806
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450920) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450922) 248
        /\ L5.u8_at RSEGS M' ((V 33%nat) + 8) 1
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450885) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450884) 248
        /\ L5.defined M' ((V 50%nat) + 8) 504).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G18 G19 G20 G21 G22 G23 G25 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 pvzI9 K14 K15 K16 K17 K18 K19 pvzI10 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K13l; move K13l before pvzI9; pose proof (proj2 pvzI9) as K13r; move K13r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K20l; move K20l before pvzI10; pose proof (proj2 pvzI10) as K20r; move K20r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PawvY5c.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvY5c.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvY5c.kn0).
  { unfold know_ok, PawvY5c.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K24 K25; lia | clear - HV2l HV2r K3l K3r K12 K24 K25; lia | clear - HV2l HV2r K3l K3r K12 K24 K25; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31; lia | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31; lia | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | byte_tac ltac:(clear) | exactA K33]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvY5c.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvY5c.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 8) -> ~ ((((vz_50 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 0) + 64) -> ~ ((vz_33 + 8) <= bv_unsigned a < (vz_33 + 8) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PawvY5c.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvY5c.ps0) with 0x7b90c in Hms. change (SR.ps_regs PawvY5c.ps0) with (map (fun i => (i, nth i PawvY5c.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvY5c.ps0) with PawvY5c.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvY5c.regs0 PawvY5c.regs_out0 80 KS_awvY5c KS_awvY5c_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvY5c.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PawvY5c.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvY5c.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvY5c.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvY5c.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvY5c.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvY5c.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PawvY5c.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

End PNARVBP.
