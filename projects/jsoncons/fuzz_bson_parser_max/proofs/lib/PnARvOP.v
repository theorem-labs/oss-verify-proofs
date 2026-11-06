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
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.seg Require LibSegBa_awvO0 LibSegBa_awvO1 LibSegBa_awvOc LibSegBa_awvO2 LibSegBa_awvO3 LibSegBa_awvO4 LibSegBa_awvO5 LibSegBa_awvO6 LibSegBa_awvO7.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNARVOP.
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
Module PawvO0 := LibSegBa_awvO0.
Definition KS_awvO0 : list nat := Eval vm_compute in (BG.kept_list 130 PawvO0.regs0 PawvO0.regs_out0).
Lemma KS_awvO0_ok : BG.kept_ok 130 PawvO0.regs0 PawvO0.regs_out0 KS_awvO0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvO0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 224) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 224) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 26) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  140735332487392 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 224) 224 -> 6897664 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 -> 6897664 <= (V 50%nat) <= 140737488354816 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 512 ->
  L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 50%nat) + 504) (V 51%nat) ->
  4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 512 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) ->
  (((V 2%nat) - 224) + 224 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 224)) -> (((V 2%nat) - 224) + 224 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 224)) -> (65536 + 6832128 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) -> (65536 + 6832128 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= 65536) ->
  (65536 + 6832128 <= (V 51%nat) \/ (V 51%nat) + 1 <= 65536) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((((V 50%nat) / 8) + 2147450880) + 52) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 52) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((((V 50%nat) / 8) + 2147450880) + 52) <= i < ((((V 50%nat) / 8) + 2147450880) + 52) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xaf3d4 M) (st fx' R' 0xadae0 M')
        /\ (forall x, In x KS_awvO0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 717812
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 50%nat) + 416)
        /\ getr R' (reg 12) = Z_to_bv 64 12
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 50%nat) + 416)
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450933) 4
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450932) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G18 G19 G20 G21 G22 G26 G27 pvzI7 K1 K2 pvzI8 K4 pvzI9 K6 K7 K8 K9 K10 K11 pvzI10 K13 K14 K15 K16 K17 K18 K19 K20.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K5l; move K5l before pvzI9; pose proof (proj2 pvzI9) as K5r; move K5r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K12l; move K12l before pvzI10; pose proof (proj2 pvzI10) as K12r; move K12r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PawvO0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvO0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvO0.kn0).
  { unfold know_ok, PawvO0.kn0.
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
  pvz_hg ltac:(idtac; destruct (PawvO0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvO0.NX0 with 130%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((vz_50 / 8) + 2147450880) + 52) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 52) + 2) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PawvO0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvO0.ps0) with 0xadae0 in Hms. change (SR.ps_regs PawvO0.ps0) with (map (fun i => (i, nth i PawvO0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvO0.ps0) with PawvO0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvO0.regs0 PawvO0.regs_out0 130 KS_awvO0 KS_awvO0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvO0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PawvO0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvO0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvO0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvO0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvO0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvO0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PawvO0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvO0.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PawvO0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvO1 := LibSegBa_awvO1.
Definition KS_awvO1_0 : list nat := Eval vm_compute in (BG.kept_list 130 PawvO1.regs0 PawvO1.regs_out0).
Lemma KS_awvO1_0_ok : BG.kept_ok 130 PawvO1.regs0 PawvO1.regs_out0 KS_awvO1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_awvO1_1 : list nat := Eval vm_compute in (BG.kept_list 130 PawvO1.regs0 PawvO1.regs_out1).
Lemma KS_awvO1_1_ok : BG.kept_ok 130 PawvO1.regs0 PawvO1.regs_out1 KS_awvO1_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvO1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 224) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 224) -> getr R (reg 10) = Z_to_bv 64 (V 37%nat) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 50%nat) + 416) -> getr R (reg 26) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1269760 -> L5.u64_at RSEGS M 1300408 2147450880 -> L5.u32_at RSEGS M 1300416 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 224) 224 -> 6897664 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M ((((V 33%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 400) / 8) + 2147450880) 1 ->
  (((V 2%nat) - 224) + 224 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 224)) -> 6897664 <= (V 50%nat) <= 140737488354816 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 512 ->
  L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 50%nat) + 504) (V 51%nat) ->
  4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 512 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) ->
  (((V 2%nat) - 224) + 224 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 224)) -> (((V 2%nat) - 224) + 224 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 224)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 512 <= (V 33%nat)) -> ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) ->
  ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= (((V 33%nat) / 8) + 2147450880)) -> (65536 + 6832128 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) -> (65536 + 6832128 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= 65536) -> (65536 + 6832128 <= (V 51%nat) \/ (V 51%nat) + 1 <= 65536) ->
  L5.u64_at RSEGS M ((V 33%nat) + 400) (V 38%nat) -> 4136 <= (V 38%nat) <= 140737488355328 -> (65536 + 6832128 <= ((V 38%nat) - 40) \/ ((V 38%nat) - 40) + 40 <= 65536) -> aligned (V 38%nat) 8 ->
  L5.u64_at RSEGS M ((V 38%nat) - 24) (V 39%nat) -> (2147446784 + 17592186048512 <= ((V 38%nat) - 40) \/ ((V 38%nat) - 40) + 40 <= 2147446784) -> L5KA.zeros_at M ((((V 38%nat) - 24) / 8) + 2147450880) 1 -> (((V 2%nat) - 224) + 224 <= ((V 38%nat) - 40) \/ ((V 38%nat) - 40) + 40 <= ((V 2%nat) - 224)) ->
  (((V 38%nat) - 40) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 38%nat) - 40)) -> (((V 38%nat) - 40) + 40 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 38%nat) - 40)) -> (((V 38%nat) - 40) + 40 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 38%nat) - 40)) -> (((((V 38%nat) - 24) / 8) + 2147450880) + 1 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= ((((V 38%nat) - 24) / 8) + 2147450880)) ->
  L5.writable RSEGS M ((V 38%nat) - 24) 8 -> 0 <= (V 37%nat) <= 12 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 38%nat) - 24) <= bv_unsigned a < ((V 38%nat) - 24) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 38%nat) - 24) <= i < ((V 38%nat) - 24) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xaf3f4 M) (st fx' R' 0xaf440 M')
        /\ (forall x, In x KS_awvO1_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 38%nat) - 24)
        /\ bv_unsigned (getr R' (reg 12)) = (((V 37%nat) + (V 39%nat)) mod 2 ^ 64)
        /\ getr R' (reg 13) = Z_to_bv 64 12
        /\ getr R' (reg 24) = Z_to_bv 64 (V 36%nat)
        /\ (((V 37%nat) - 12) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 38%nat) - 24) (((V 37%nat) + (V 39%nat)) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xaf3f4 M) (st fx' R' 0xad694 M')
        /\ (forall x, In x KS_awvO1_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 721336
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ bv_unsigned (getr R' (reg 12)) = (((V 37%nat) + (V 39%nat)) mod 2 ^ 64)
        /\ getr R' (reg 13) = Z_to_bv 64 12
        /\ getr R' (reg 24) = Z_to_bv 64 (V 36%nat)
        /\ 1 <= (((V 37%nat) - 12) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 38%nat) - 24) (((V 37%nat) + (V 39%nat)) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI10 K4 K5 pvzI11 K7 K8 K9 K10 K11 K12 pvzI12 K14 K15 K16 K17 K18 K19 pvzI13 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 pvzI14 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 pvzI15.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV39l; move HV39l before pvzI7; pose proof (proj2 pvzI7) as HV39r; move HV39r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV50l; move HV50l before pvzI8; pose proof (proj2 pvzI8) as HV50r; move HV50r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV51l; move HV51l before pvzI9; pose proof (proj2 pvzI9) as HV51r; move HV51r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K6l; move K6l before pvzI11; pose proof (proj2 pvzI11) as K6r; move K6r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K13l; move K13l before pvzI12; pose proof (proj2 pvzI12) as K13r; move K13r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K20l; move K20l before pvzI13; pose proof (proj2 pvzI13) as K20r; move K20r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K33l; move K33l before pvzI14; pose proof (proj2 pvzI14) as K33r; move K33r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K45l; move K45l before pvzI15; pose proof (proj2 pvzI15) as K45r; move K45r before pvzI15; clear pvzI15.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PawvO1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvO1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvO1.kn0).
  { unfold know_ok, PawvO1.kn0.
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
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvO1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvO1.NX0 with 130%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_38 - 24) <= bv_unsigned a < (vz_38 - 24) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PawvO1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | evalEk' ZA Hag ltac:(clear) | clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PawvO1.ps0) with 0xaf440 in Hms. change (SR.ps_regs PawvO1.ps0) with (map (fun i => (i, nth i PawvO1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PawvO1.ps0) with PawvO1.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvO1.regs0 PawvO1.regs_out0 130 KS_awvO1_0 KS_awvO1_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PawvO1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvO1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PawvO1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PawvO1.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PawvO1.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PawvO1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PawvO1.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PawvO1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. 
  - right.
    change (SR.ps_pc PawvO1.ps1) with 0xad694 in Hms. change (SR.ps_regs PawvO1.ps1) with (map (fun i => (i, nth i PawvO1.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PawvO1.ps1) with PawvO1.cells1 in Hcells. unfold PawvO1.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvO1.regs0 PawvO1.regs_out1 130 KS_awvO1_1 KS_awvO1_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PawvO1.regs_out1 E' R' 1 Hregs) by (clear; lia). cbn [nth PawvO1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PawvO1.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvO1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PawvO1.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvO1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PawvO1.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PawvO1.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PawvO1.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PawvO1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PawvO1.regs_out1 E' R' 24 Hregs) by (clear; lia). cbn [nth PawvO1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV38l HV38r K33l K33r K34 K37 K39 K40 K41 K42 K43) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvOc := LibSegBa_awvOc.
Definition KS_awvOc : list nat := Eval vm_compute in (BG.kept_list 130 PawvOc.regs0 PawvOc.regs_out0).
Lemma KS_awvOc_ok : BG.kept_ok 130 PawvOc.regs0 PawvOc.regs_out0 KS_awvOc = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvOc_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 224) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 224) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 50%nat) + 416) -> getr R (reg 24) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1269760 -> L5.u64_at RSEGS M 1300408 2147450880 -> L5.u32_at RSEGS M 1300416 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 224) 224 -> 6897664 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M ((((V 33%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 400) / 8) + 2147450880) 1 ->
  (((V 2%nat) - 224) + 224 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 224)) -> 6897664 <= (V 50%nat) <= 140737488354816 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 512 ->
  L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 50%nat) + 504) (V 51%nat) ->
  4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 512 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) ->
  (((V 2%nat) - 224) + 224 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 224)) -> (((V 2%nat) - 224) + 224 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 224)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 512 <= (V 33%nat)) -> ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) ->
  ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= (((V 33%nat) / 8) + 2147450880)) -> (65536 + 6832128 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) -> (65536 + 6832128 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= 65536) -> (65536 + 6832128 <= (V 51%nat) \/ (V 51%nat) + 1 <= 65536) ->
  L5.writable RSEGS M ((V 33%nat) + 8) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 64) -> ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 64) -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb01b8 M) (st fx' R' 0x7b544 M')
        /\ (forall x, In x KS_awvOc -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 720824
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880)
        /\ getr R' (reg 11) = Z_to_bv 64 64
        /\ L5.u64_at RSEGS M' (V 50%nat) 1172321806
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450933) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450932) 248
        /\ L5.u8_at RSEGS M' ((V 33%nat) + 8) 0
        /\ L5.defined M' ((V 50%nat) + 8) 504).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 pvzI9 K14 K15 K16 K17 K18 K19 pvzI10 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K13l; move K13l before pvzI9; pose proof (proj2 pvzI9) as K13r; move K13r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K20l; move K20l before pvzI10; pose proof (proj2 pvzI10) as K20r; move K20r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PawvOc.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvOc.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvOc.kn0).
  { unfold know_ok, PawvOc.kn0.
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
  pvz_hg ltac:(idtac; destruct (PawvOc.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvOc.NX0 with 130%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 8) -> ~ ((((vz_50 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 0) + 64) -> ~ ((vz_33 + 8) <= bv_unsigned a < (vz_33 + 8) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PawvOc.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvOc.ps0) with 0x7b544 in Hms. change (SR.ps_regs PawvOc.ps0) with (map (fun i => (i, nth i PawvOc.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvOc.ps0) with PawvOc.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvOc.regs0 PawvOc.regs_out0 130 KS_awvOc KS_awvOc_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvOc.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PawvOc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvOc.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvOc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvOc.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvOc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvO2 := LibSegBa_awvO2.
Definition KS_awvO2 : list nat := Eval vm_compute in (BG.kept_list 130 PawvO2.regs0 PawvO2.regs_out0).
Lemma KS_awvO2_ok : BG.kept_ok 130 PawvO2.regs0 PawvO2.regs_out0 KS_awvO2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvO2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 80%nat) < 2 ^ 64 -> 0 <= (V 81%nat) < 2 ^ 64 -> 0 <= (V 82%nat) < 2 ^ 64 -> 0 <= (V 83%nat) < 2 ^ 64 -> 0 <= (V 84%nat) < 2 ^ 64 -> 0 <= (V 85%nat) < 2 ^ 64 -> 0 <= (V 86%nat) < 2 ^ 64 -> 0 <= (V 87%nat) < 2 ^ 64 -> 0 <= (V 88%nat) < 2 ^ 64 -> 0 <= (V 89%nat) < 2 ^ 64 -> 0 <= (V 90%nat) < 2 ^ 64 -> 0 <= (V 91%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 224) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 224) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 50%nat) + 416) -> getr R (reg 24) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1269760 -> L5.u64_at RSEGS M 1300408 2147450880 -> L5.u32_at RSEGS M 1300416 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 224) 224 -> 6897664 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M ((((V 33%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 400) / 8) + 2147450880) 1 ->
  (((V 2%nat) - 224) + 224 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 224)) -> 6897664 <= (V 50%nat) <= 140737488354816 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 512 ->
  L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 50%nat) + 504) (V 51%nat) ->
  4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 512 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) ->
  (((V 2%nat) - 224) + 224 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 224)) -> (((V 2%nat) - 224) + 224 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 224)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 512 <= (V 33%nat)) -> ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) ->
  ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= (((V 33%nat) / 8) + 2147450880)) -> (65536 + 6832128 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) -> (65536 + 6832128 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= 65536) -> (65536 + 6832128 <= (V 51%nat) \/ (V 51%nat) + 1 <= 65536) ->
  L5.u8_at RSEGS M ((V 50%nat) + 416) (V 80%nat) -> 0 <= (V 80%nat) <= 255 -> L5.u8_at RSEGS M ((V 50%nat) + 417) (V 81%nat) -> 0 <= (V 81%nat) <= 255 ->
  L5.u8_at RSEGS M ((V 50%nat) + 418) (V 82%nat) -> 0 <= (V 82%nat) <= 255 -> L5.u8_at RSEGS M ((V 50%nat) + 419) (V 83%nat) -> 0 <= (V 83%nat) <= 255 ->
  L5.u8_at RSEGS M ((V 50%nat) + 420) (V 84%nat) -> 0 <= (V 84%nat) <= 255 -> L5.u8_at RSEGS M ((V 50%nat) + 421) (V 85%nat) -> 0 <= (V 85%nat) <= 255 ->
  L5.u8_at RSEGS M ((V 50%nat) + 422) (V 86%nat) -> 0 <= (V 86%nat) <= 255 -> L5.u8_at RSEGS M ((V 50%nat) + 423) (V 87%nat) -> 0 <= (V 87%nat) <= 255 ->
  L5.u8_at RSEGS M ((V 50%nat) + 424) (V 88%nat) -> 0 <= (V 88%nat) <= 255 -> L5.u8_at RSEGS M ((V 50%nat) + 425) (V 89%nat) -> 0 <= (V 89%nat) <= 255 ->
  L5.u8_at RSEGS M ((V 50%nat) + 426) (V 90%nat) -> 0 <= (V 90%nat) <= 255 -> L5.u8_at RSEGS M ((V 50%nat) + 427) (V 91%nat) -> 0 <= (V 91%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 208) <= bv_unsigned a < ((V 2%nat) - 208) + 80) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 208) <= i < ((V 2%nat) - 208) + 80) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xaf440 M) (st fx' R' 0xd3ce0 M')
        /\ (forall x, In x KS_awvO2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 717996
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 368)
        /\ getr R' (reg 11) = Z_to_bv 64 24
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 368)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 81%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 80%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 91%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 90%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 89%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 88%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) (V 87%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) (V 86%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) (V 85%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) (V 84%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) (V 83%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (V 82%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G27 K0 K1 K2 pvzI19 K4 K5 pvzI20 K7 K8 K9 K10 K11 K12 pvzI21 K14 K15 K16 K17 K18 K19 pvzI22 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 pvzI23 K34 pvzI24 K36 pvzI25 K38 pvzI26 K40 pvzI27 K42 pvzI28 K44 pvzI29 K46 pvzI30 K48 pvzI31 K50 pvzI32 K52 pvzI33 K54 pvzI34.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV80l; move HV80l before pvzI7; pose proof (proj2 pvzI7) as HV80r; move HV80r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV81l; move HV81l before pvzI8; pose proof (proj2 pvzI8) as HV81r; move HV81r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV82l; move HV82l before pvzI9; pose proof (proj2 pvzI9) as HV82r; move HV82r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV83l; move HV83l before pvzI10; pose proof (proj2 pvzI10) as HV83r; move HV83r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV84l; move HV84l before pvzI11; pose proof (proj2 pvzI11) as HV84r; move HV84r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV85l; move HV85l before pvzI12; pose proof (proj2 pvzI12) as HV85r; move HV85r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV86l; move HV86l before pvzI13; pose proof (proj2 pvzI13) as HV86r; move HV86r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV87l; move HV87l before pvzI14; pose proof (proj2 pvzI14) as HV87r; move HV87r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV88l; move HV88l before pvzI15; pose proof (proj2 pvzI15) as HV88r; move HV88r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV89l; move HV89l before pvzI16; pose proof (proj2 pvzI16) as HV89r; move HV89r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV90l; move HV90l before pvzI17; pose proof (proj2 pvzI17) as HV90r; move HV90r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV91l; move HV91l before pvzI18; pose proof (proj2 pvzI18) as HV91r; move HV91r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K3l; move K3l before pvzI19; pose proof (proj2 pvzI19) as K3r; move K3r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K6l; move K6l before pvzI20; pose proof (proj2 pvzI20) as K6r; move K6r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K13l; move K13l before pvzI21; pose proof (proj2 pvzI21) as K13r; move K13r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K20l; move K20l before pvzI22; pose proof (proj2 pvzI22) as K20r; move K20r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K33l; move K33l before pvzI23; pose proof (proj2 pvzI23) as K33r; move K33r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K35l; move K35l before pvzI24; pose proof (proj2 pvzI24) as K35r; move K35r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K37l; move K37l before pvzI25; pose proof (proj2 pvzI25) as K37r; move K37r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K39l; move K39l before pvzI26; pose proof (proj2 pvzI26) as K39r; move K39r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as K41l; move K41l before pvzI27; pose proof (proj2 pvzI27) as K41r; move K41r before pvzI27; clear pvzI27. pose proof (proj1 pvzI28) as K43l; move K43l before pvzI28; pose proof (proj2 pvzI28) as K43r; move K43r before pvzI28; clear pvzI28. pose proof (proj1 pvzI29) as K45l; move K45l before pvzI29; pose proof (proj2 pvzI29) as K45r; move K45r before pvzI29; clear pvzI29. pose proof (proj1 pvzI30) as K47l; move K47l before pvzI30; pose proof (proj2 pvzI30) as K47r; move K47r before pvzI30; clear pvzI30. pose proof (proj1 pvzI31) as K49l; move K49l before pvzI31; pose proof (proj2 pvzI31) as K49r; move K49r before pvzI31; clear pvzI31. pose proof (proj1 pvzI32) as K51l; move K51l before pvzI32; pose proof (proj2 pvzI32) as K51r; move K51r before pvzI32; clear pvzI32. pose proof (proj1 pvzI33) as K53l; move K53l before pvzI33; pose proof (proj2 pvzI33) as K53r; move K53r before pvzI33; clear pvzI33. pose proof (proj1 pvzI34) as K55l; move K55l before pvzI34; pose proof (proj2 pvzI34) as K55r; move K55r before pvzI34; clear pvzI34.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_80 := V 80%nat) in *. set (vz_81 := V 81%nat) in *. set (vz_82 := V 82%nat) in *. set (vz_83 := V 83%nat) in *. set (vz_84 := V 84%nat) in *. set (vz_85 := V 85%nat) in *. set (vz_86 := V 86%nat) in *. set (vz_87 := V 87%nat) in *. set (vz_88 := V 88%nat) in *. set (vz_89 := V 89%nat) in *. set (vz_90 := V 90%nat) in *. set (vz_91 := V 91%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 80%nat => Z_to_bv 64 vz_80 | 81%nat => Z_to_bv 64 vz_81 | 82%nat => Z_to_bv 64 vz_82 | 83%nat => Z_to_bv 64 vz_83 | 84%nat => Z_to_bv 64 vz_84 | 85%nat => Z_to_bv 64 vz_85 | 86%nat => Z_to_bv 64 vz_86 | 87%nat => Z_to_bv 64 vz_87 | 88%nat => Z_to_bv 64 vz_88 | 89%nat => Z_to_bv 64 vz_89 | 90%nat => Z_to_bv 64 vz_90 | 91%nat => Z_to_bv 64 vz_91 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | 80%nat => vz_80 | 81%nat => vz_81 | 82%nat => vz_82 | 83%nat => vz_83 | 84%nat => vz_84 | 85%nat => vz_85 | 86%nat => vz_86 | 87%nat => vz_87 | 88%nat => vz_88 | 89%nat => vz_89 | 90%nat => vz_90 | 91%nat => vz_91 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 92%nat. }
  assert (HR: regs_ok E PawvO2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvO2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvO2.kn0).
  { unfold know_ok, PawvO2.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear - HV80l HV80r K33l K33r) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | byte_tac ltac:(clear - HV80l HV80r K33l K33r) | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV80l HV80r K33l K33r) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear - HV81l HV81r K35l K35r) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | byte_tac ltac:(clear - HV81l HV81r K35l K35r) | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV81l HV81r K35l K35r) | exact (conj K35l K35r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear - HV82l HV82r K37l K37r) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | byte_tac ltac:(clear - HV82l HV82r K37l K37r) | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV82l HV82r K37l K37r) | exact (conj K37l K37r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear - HV83l HV83r K39l K39r) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | byte_tac ltac:(clear - HV83l HV83r K39l K39r) | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV83l HV83r K39l K39r) | exact (conj K39l K39r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear - HV84l HV84r K41l K41r) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | byte_tac ltac:(clear - HV84l HV84r K41l K41r) | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV84l HV84r K41l K41r) | exact (conj K41l K41r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear - HV85l HV85r K43l K43r) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | byte_tac ltac:(clear - HV85l HV85r K43l K43r) | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV85l HV85r K43l K43r) | exact (conj K43l K43r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear - HV86l HV86r K45l K45r) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | byte_tac ltac:(clear - HV86l HV86r K45l K45r) | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV86l HV86r K45l K45r) | exact (conj K45l K45r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear - HV87l HV87r K47l K47r) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | byte_tac ltac:(clear - HV87l HV87r K47l K47r) | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV87l HV87r K47l K47r) | exact (conj K47l K47r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear - HV88l HV88r K49l K49r) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | byte_tac ltac:(clear - HV88l HV88r K49l K49r) | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV88l HV88r K49l K49r) | exact (conj K49l K49r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear - HV89l HV89r K51l K51r) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | byte_tac ltac:(clear - HV89l HV89r K51l K51r) | exactA K50]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV89l HV89r K51l K51r) | exact (conj K51l K51r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear - HV90l HV90r K53l K53r) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | byte_tac ltac:(clear - HV90l HV90r K53l K53r) | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV90l HV90r K53l K53r) | exact (conj K53l K53r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear - HV91l HV91r K55l K55r) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | byte_tac ltac:(clear - HV91l HV91r K55l K55r) | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV91l HV91r K55l K55r) | exact (conj K55l K55r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvO2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvO2.NX0 with 130%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 208) <= bv_unsigned a < (vz_2 - 208) + 80) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PawvO2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K24 K25 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvO2.ps0) with 0xd3ce0 in Hms. change (SR.ps_regs PawvO2.ps0) with (map (fun i => (i, nth i PawvO2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvO2.ps0) with PawvO2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvO2.regs0 PawvO2.regs_out0 130 KS_awvO2 KS_awvO2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvO2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PawvO2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvO2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvO2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvO2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvO2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvO2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PawvO2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvO2.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PawvO2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvO2.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PawvO2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvO2.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PawvO2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | evalEk' ZA Hag ltac:(clear - HV91l HV91r K55l K55r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | evalEk' ZA Hag ltac:(clear - HV90l HV90r K53l K53r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | evalEk' ZA Hag ltac:(clear - HV89l HV89r K51l K51r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | evalEk' ZA Hag ltac:(clear - HV88l HV88r K49l K49r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | evalEk' ZA Hag ltac:(clear - HV87l HV87r K47l K47r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | evalEk' ZA Hag ltac:(clear - HV86l HV86r K45l K45r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | evalEk' ZA Hag ltac:(clear - HV85l HV85r K43l K43r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | evalEk' ZA Hag ltac:(clear - HV84l HV84r K41l K41r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | evalEk' ZA Hag ltac:(clear - HV83l HV83r K39l K39r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | evalEk' ZA Hag ltac:(clear - HV82l HV82r K37l K37r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvO3 := LibSegBa_awvO3.
Definition KS_awvO3 : list nat := Eval vm_compute in (BG.kept_list 130 PawvO3.regs0 PawvO3.regs_out0).
Lemma KS_awvO3_ok : BG.kept_ok 130 PawvO3.regs0 PawvO3.regs_out0 KS_awvO3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvO3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 80%nat) < 2 ^ 64 -> 0 <= (V 81%nat) < 2 ^ 64 -> 0 <= (V 82%nat) < 2 ^ 64 -> 0 <= (V 83%nat) < 2 ^ 64 -> 0 <= (V 100%nat) < 2 ^ 64 -> 0 <= (V 101%nat) < 2 ^ 64 -> 0 <= (V 102%nat) < 2 ^ 64 -> 0 <= (V 103%nat) < 2 ^ 64 -> 0 <= (V 112%nat) < 2 ^ 64 -> 0 <= (V 113%nat) < 2 ^ 64 -> 0 <= (V 114%nat) < 2 ^ 64 -> 0 <= (V 115%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 224) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 224) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 33%nat) + 368) -> getr R (reg 24) = Z_to_bv 64 (V 36%nat) -> getr R (reg 25) = Z_to_bv 64 (V 81%nat) -> getr R (reg 26) = Z_to_bv 64 (V 80%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1269760 -> L5.u64_at RSEGS M 1300408 2147450880 -> L5.u32_at RSEGS M 1300416 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 224) 224 -> 6897664 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M ((((V 33%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 400) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 368) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 384) / 8) + 2147450880) 1 -> (((V 2%nat) - 224) + 224 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 224)) -> 6897664 <= (V 50%nat) <= 140737488354816 ->
  aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 512 -> L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) ->
  L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 50%nat) + 504) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 512 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 224) + 224 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 224)) -> (((V 2%nat) - 224) + 224 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 224)) ->
  ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 512 <= (V 33%nat)) -> ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= (((V 33%nat) / 8) + 2147450880)) -> (65536 + 6832128 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) ->
  (65536 + 6832128 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= 65536) -> (65536 + 6832128 <= (V 51%nat) \/ (V 51%nat) + 1 <= 65536) -> 4096 <= (V 57%nat) <= 140737488355296 -> aligned (V 57%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 57%nat) \/ (V 57%nat) + 24 <= 2147446784) -> L5.writable RSEGS M (V 57%nat) 24 -> (((V 2%nat) - 224) + 224 <= (V 57%nat) \/ (V 57%nat) + 24 <= ((V 2%nat) - 224)) -> ((V 57%nat) + 24 <= (V 33%nat) \/ (V 33%nat) + 416 <= (V 57%nat)) ->
  (65536 + 6832128 <= (V 57%nat) \/ (V 57%nat) + 24 <= 65536) -> ((V 57%nat) + 24 <= (V 50%nat) \/ (V 50%nat) + 512 <= (V 57%nat)) -> ((V 57%nat) + 24 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 57%nat)) -> L5KA.zeros_at M (((V 57%nat) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 57%nat) + 2) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 57%nat) + 4) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 57%nat) + 6) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 57%nat) + 8) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 57%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 57%nat) + 12) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 57%nat) + 14) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 57%nat) + 16) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 57%nat) + 18) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 57%nat) + 20) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 57%nat) + 22) / 8) + 2147450880) 1 -> L5.u8_at RSEGS M ((V 33%nat) + 368) (V 56%nat) ->
  0 <= (V 56%nat) <= 255 -> Z.testbit (V 56%nat) 0 = true -> L5.u64_at RSEGS M ((V 33%nat) + 384) (V 57%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 376) (V 58%nat) ->
  0 <= (V 80%nat) <= 255 -> L5.u8_at RSEGS M ((2 * (V 80%nat)) + 145760) (V 100%nat) -> 0 <= (V 100%nat) <= 255 -> L5.u8_at RSEGS M ((2 * (V 80%nat)) + 145761) (V 112%nat) ->
  0 <= (V 112%nat) <= 255 -> L5KA.zeros_at M ((((2 * (V 80%nat)) + 145760) / 8) + 2147450880) 1 -> 0 <= (V 81%nat) <= 255 -> L5.u8_at RSEGS M ((2 * (V 81%nat)) + 145760) (V 101%nat) ->
  0 <= (V 101%nat) <= 255 -> L5.u8_at RSEGS M ((2 * (V 81%nat)) + 145761) (V 113%nat) -> 0 <= (V 113%nat) <= 255 -> L5KA.zeros_at M ((((2 * (V 81%nat)) + 145760) / 8) + 2147450880) 1 ->
  0 <= (V 82%nat) <= 255 -> L5.u8_at RSEGS M ((2 * (V 82%nat)) + 145760) (V 102%nat) -> 0 <= (V 102%nat) <= 255 -> L5.u8_at RSEGS M ((2 * (V 82%nat)) + 145761) (V 114%nat) ->
  0 <= (V 114%nat) <= 255 -> L5KA.zeros_at M ((((2 * (V 82%nat)) + 145760) / 8) + 2147450880) 1 -> 0 <= (V 83%nat) <= 255 -> L5.u8_at RSEGS M ((2 * (V 83%nat)) + 145760) (V 103%nat) ->
  0 <= (V 103%nat) <= 255 -> L5.u8_at RSEGS M ((2 * (V 83%nat)) + 145761) (V 115%nat) -> 0 <= (V 115%nat) <= 255 -> L5KA.zeros_at M ((((2 * (V 83%nat)) + 145760) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M ((V 2%nat) - 208) (V 82%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 200) (V 83%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 57%nat) + 0) <= bv_unsigned a < ((V 57%nat) + 0) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 57%nat) + 0) <= i < ((V 57%nat) + 0) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xaf4ac M) (st fx' R' 0xafc24 M')
        /\ (forall x, In x KS_awvO3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 57%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 57%nat) + 6)
        /\ getr R' (reg 13) = Z_to_bv 64 ((((V 33%nat) + 368) / 8) + 2147450880)
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 17) = Z_to_bv 64 145760).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 pvzI20 pvzI21 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI22 K4 K5 pvzI23 K7 K8 K9 K10 K11 K12 K13 K14 pvzI24 K16 K17 K18 K19 K20 K21 pvzI25 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 pvzI26 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 K55 pvzI27 K57 K58 K59 pvzI28 K61 pvzI29 K63 pvzI30 K65 pvzI31 K67 pvzI32 K69 pvzI33 K71 pvzI34 K73 pvzI35 K75 pvzI36 K77 pvzI37 K79 pvzI38 K81 pvzI39 K83 K84 K85.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV56l; move HV56l before pvzI7; pose proof (proj2 pvzI7) as HV56r; move HV56r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV57l; move HV57l before pvzI8; pose proof (proj2 pvzI8) as HV57r; move HV57r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV58l; move HV58l before pvzI9; pose proof (proj2 pvzI9) as HV58r; move HV58r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV80l; move HV80l before pvzI10; pose proof (proj2 pvzI10) as HV80r; move HV80r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV81l; move HV81l before pvzI11; pose proof (proj2 pvzI11) as HV81r; move HV81r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV82l; move HV82l before pvzI12; pose proof (proj2 pvzI12) as HV82r; move HV82r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV83l; move HV83l before pvzI13; pose proof (proj2 pvzI13) as HV83r; move HV83r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV100l; move HV100l before pvzI14; pose proof (proj2 pvzI14) as HV100r; move HV100r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV101l; move HV101l before pvzI15; pose proof (proj2 pvzI15) as HV101r; move HV101r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV102l; move HV102l before pvzI16; pose proof (proj2 pvzI16) as HV102r; move HV102r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV103l; move HV103l before pvzI17; pose proof (proj2 pvzI17) as HV103r; move HV103r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV112l; move HV112l before pvzI18; pose proof (proj2 pvzI18) as HV112r; move HV112r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV113l; move HV113l before pvzI19; pose proof (proj2 pvzI19) as HV113r; move HV113r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as HV114l; move HV114l before pvzI20; pose proof (proj2 pvzI20) as HV114r; move HV114r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as HV115l; move HV115l before pvzI21; pose proof (proj2 pvzI21) as HV115r; move HV115r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K3l; move K3l before pvzI22; pose proof (proj2 pvzI22) as K3r; move K3r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K6l; move K6l before pvzI23; pose proof (proj2 pvzI23) as K6r; move K6r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K15l; move K15l before pvzI24; pose proof (proj2 pvzI24) as K15r; move K15r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K22l; move K22l before pvzI25; pose proof (proj2 pvzI25) as K22r; move K22r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K34l; move K34l before pvzI26; pose proof (proj2 pvzI26) as K34r; move K34r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as K56l; move K56l before pvzI27; pose proof (proj2 pvzI27) as K56r; move K56r before pvzI27; clear pvzI27. pose proof (proj1 pvzI28) as K60l; move K60l before pvzI28; pose proof (proj2 pvzI28) as K60r; move K60r before pvzI28; clear pvzI28. pose proof (proj1 pvzI29) as K62l; move K62l before pvzI29; pose proof (proj2 pvzI29) as K62r; move K62r before pvzI29; clear pvzI29. pose proof (proj1 pvzI30) as K64l; move K64l before pvzI30; pose proof (proj2 pvzI30) as K64r; move K64r before pvzI30; clear pvzI30. pose proof (proj1 pvzI31) as K66l; move K66l before pvzI31; pose proof (proj2 pvzI31) as K66r; move K66r before pvzI31; clear pvzI31. pose proof (proj1 pvzI32) as K68l; move K68l before pvzI32; pose proof (proj2 pvzI32) as K68r; move K68r before pvzI32; clear pvzI32. pose proof (proj1 pvzI33) as K70l; move K70l before pvzI33; pose proof (proj2 pvzI33) as K70r; move K70r before pvzI33; clear pvzI33. pose proof (proj1 pvzI34) as K72l; move K72l before pvzI34; pose proof (proj2 pvzI34) as K72r; move K72r before pvzI34; clear pvzI34. pose proof (proj1 pvzI35) as K74l; move K74l before pvzI35; pose proof (proj2 pvzI35) as K74r; move K74r before pvzI35; clear pvzI35. pose proof (proj1 pvzI36) as K76l; move K76l before pvzI36; pose proof (proj2 pvzI36) as K76r; move K76r before pvzI36; clear pvzI36. pose proof (proj1 pvzI37) as K78l; move K78l before pvzI37; pose proof (proj2 pvzI37) as K78r; move K78r before pvzI37; clear pvzI37. pose proof (proj1 pvzI38) as K80l; move K80l before pvzI38; pose proof (proj2 pvzI38) as K80r; move K80r before pvzI38; clear pvzI38. pose proof (proj1 pvzI39) as K82l; move K82l before pvzI39; pose proof (proj2 pvzI39) as K82r; move K82r before pvzI39; clear pvzI39.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *. set (vz_80 := V 80%nat) in *. set (vz_81 := V 81%nat) in *. set (vz_82 := V 82%nat) in *. set (vz_83 := V 83%nat) in *. set (vz_100 := V 100%nat) in *. set (vz_101 := V 101%nat) in *. set (vz_102 := V 102%nat) in *. set (vz_103 := V 103%nat) in *. set (vz_112 := V 112%nat) in *. set (vz_113 := V 113%nat) in *. set (vz_114 := V 114%nat) in *. set (vz_115 := V 115%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | 80%nat => Z_to_bv 64 vz_80 | 81%nat => Z_to_bv 64 vz_81 | 82%nat => Z_to_bv 64 vz_82 | 83%nat => Z_to_bv 64 vz_83 | 100%nat => Z_to_bv 64 vz_100 | 101%nat => Z_to_bv 64 vz_101 | 102%nat => Z_to_bv 64 vz_102 | 103%nat => Z_to_bv 64 vz_103 | 112%nat => Z_to_bv 64 vz_112 | 113%nat => Z_to_bv 64 vz_113 | 114%nat => Z_to_bv 64 vz_114 | 115%nat => Z_to_bv 64 vz_115 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | 56%nat => vz_56 | 57%nat => vz_57 | 58%nat => vz_58 | 80%nat => vz_80 | 81%nat => vz_81 | 82%nat => vz_82 | 83%nat => vz_83 | 100%nat => vz_100 | 101%nat => vz_101 | 102%nat => vz_102 | 103%nat => vz_103 | 112%nat => vz_112 | 113%nat => vz_113 | 114%nat => vz_114 | 115%nat => vz_115 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 116%nat. }
  assert (HR: regs_ok E PawvO3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvO3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvO3.kn0).
  { unfold know_ok, PawvO3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K14 K26 K27 K38) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K14 K26 K27 K38) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K14 K26 K27 K38) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K14 K26 K27 K38; lia | clear - HV2l HV2r K3l K3r K14 K26 K27 K38; lia | clear - HV2l HV2r K3l K3r K14 K26 K27 K38; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30 K39) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30 K39) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30 K39) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30 K39) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30 K39; lia | clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30 K39; lia | clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30 K39; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30 K39) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30 K39; lia | clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30 K39; lia | clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30 K39; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30 K39) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30 K39; lia | clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30 K39; lia | clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30 K39; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30 K39) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30 K39; lia | clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30 K39; lia | clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30 K39; lia | exactA K12]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30 K39) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30 K39; lia | clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30 K39; lia | clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30 K39; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K14 K26 K27 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30 K39) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32 K41) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32 K41) | clear; lia | exact K16]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32 K41) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32 K41; lia | clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32 K41; lia | clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32 K41; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32 K41) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32 K41; lia | clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32 K41; lia | clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32 K41; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32 K41) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32 K41) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32 K41; lia | clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32 K41; lia | clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32 K41; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32 K41) | evalEk ZA ltac:(clear - HV51l HV51r K22l K22r K24 K25 K27 K29 K33 K42) | clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32 K41; lia | clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32 K41; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K22l K22r K24 K25 K27 K29 K33 K42) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K22l K22r K24 K25 K27 K29 K33 K42) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K22l K22r K24 K25 K27 K29 K33 K42; lia | clear - HV51l HV51r K22l K22r K24 K25 K27 K29 K33 K42; lia | clear - HV51l HV51r K22l K22r K24 K25 K27 K29 K33 K42; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K22l K22r K24 K25 K27 K29 K33 K42) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32 K41) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K22l K22r K24 K25 K27 K29 K33 K42) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K14 K26 K27 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32 K41) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K14 K26 K27 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K22l K22r K24 K25 K27 K29 K33 K42) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32 K41) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K22l K22r K24 K25 K27 K29 K33 K42) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32 K41) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32 K41) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32 K41) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K22l K22r K24 K25 K27 K29 K33 K42) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42) | exact (conj K34l K34r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42) | clear; lia | exact K35]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42; lia | clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42; lia | clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K14 K26 K27 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30 K39) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32 K41) | evalEk ZA ltac:(clear) | generalize K41; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K22l K22r K24 K25 K27 K29 K33 K42) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42; lia | clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42; lia | clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42; lia | exactA K43]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42; lia | clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42; lia | clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42; lia | exactA K44]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42; lia | clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42; lia | clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42; lia | exactA K45]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42; lia | clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42; lia | clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42; lia | exactA K46]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42; lia | clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42; lia | clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42; lia | exactA K47]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42; lia | clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42; lia | clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42; lia | exactA K48]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42; lia | clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42; lia | clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42; lia | exactA K49]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42; lia | clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42; lia | clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42; lia | exactA K50]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42; lia | clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42; lia | clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42; lia | exactA K51]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42; lia | clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42; lia | clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42; lia | exactA K52]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42; lia | clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42; lia | clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42; lia | exactA K53]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42; lia | clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42; lia | clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30 K39) | evalEk ZA ltac:(clear - HV56l HV56r K56l K56r K57) | clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30 K39; lia | clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30 K39; lia | byte_tac ltac:(clear - HV56l HV56r K56l K56r K57) | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV56l HV56r K56l K56r K57) | exact (conj K56l K56r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV56l HV56r K56l K56r K57) | clear; lia | rewrite (L5K.land1_bit0_true vz_56 ltac:(clear - HV56l HV56r K56l K56r K57; lia) K57); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30 K39) | evalEk ZA ltac:(clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42) | clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30 K39; lia | clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30 K39; lia | exactA K58]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30 K39) | evalEk ZA ltac:(clear - HV58l HV58r) | clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30 K39; lia | clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30 K39; lia | exactA K59]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV80l HV80r K60l K60r) | exact (conj K60l K60r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV80l HV80r K60l K60r) | evalEk ZA ltac:(clear - HV100l HV100r K62l K62r) | clear - HV80l HV80r K60l K60r; lia | clear - HV80l HV80r K60l K60r; lia | byte_tac ltac:(clear - HV100l HV100r K62l K62r) | exactA K61]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV100l HV100r K62l K62r) | exact (conj K62l K62r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV80l HV80r K60l K60r) | evalEk ZA ltac:(clear - HV112l HV112r K64l K64r) | clear - HV80l HV80r K60l K60r; lia | clear - HV80l HV80r K60l K60r; lia | byte_tac ltac:(clear - HV112l HV112r K64l K64r) | exactA K63]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV112l HV112r K64l K64r) | exact (conj K64l K64r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV80l HV80r K60l K60r) | evalEk ZA ltac:(clear) | clear - HV80l HV80r K60l K60r; lia | clear - HV80l HV80r K60l K60r; lia | clear - HV80l HV80r K60l K60r; lia | exactA K65]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV81l HV81r K66l K66r) | exact (conj K66l K66r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV81l HV81r K66l K66r) | evalEk ZA ltac:(clear - HV101l HV101r K68l K68r) | clear - HV81l HV81r K66l K66r; lia | clear - HV81l HV81r K66l K66r; lia | byte_tac ltac:(clear - HV101l HV101r K68l K68r) | exactA K67]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV101l HV101r K68l K68r) | exact (conj K68l K68r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV81l HV81r K66l K66r) | evalEk ZA ltac:(clear - HV113l HV113r K70l K70r) | clear - HV81l HV81r K66l K66r; lia | clear - HV81l HV81r K66l K66r; lia | byte_tac ltac:(clear - HV113l HV113r K70l K70r) | exactA K69]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV113l HV113r K70l K70r) | exact (conj K70l K70r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV81l HV81r K66l K66r) | evalEk ZA ltac:(clear) | clear - HV81l HV81r K66l K66r; lia | clear - HV81l HV81r K66l K66r; lia | clear - HV81l HV81r K66l K66r; lia | exactA K71]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV82l HV82r K72l K72r) | exact (conj K72l K72r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV82l HV82r K72l K72r) | evalEk ZA ltac:(clear - HV102l HV102r K74l K74r) | clear - HV82l HV82r K72l K72r; lia | clear - HV82l HV82r K72l K72r; lia | byte_tac ltac:(clear - HV102l HV102r K74l K74r) | exactA K73]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV102l HV102r K74l K74r) | exact (conj K74l K74r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV82l HV82r K72l K72r) | evalEk ZA ltac:(clear - HV114l HV114r K76l K76r) | clear - HV82l HV82r K72l K72r; lia | clear - HV82l HV82r K72l K72r; lia | byte_tac ltac:(clear - HV114l HV114r K76l K76r) | exactA K75]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV114l HV114r K76l K76r) | exact (conj K76l K76r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV82l HV82r K72l K72r) | evalEk ZA ltac:(clear) | clear - HV82l HV82r K72l K72r; lia | clear - HV82l HV82r K72l K72r; lia | clear - HV82l HV82r K72l K72r; lia | exactA K77]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV83l HV83r K78l K78r) | exact (conj K78l K78r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV83l HV83r K78l K78r) | evalEk ZA ltac:(clear - HV103l HV103r K80l K80r) | clear - HV83l HV83r K78l K78r; lia | clear - HV83l HV83r K78l K78r; lia | byte_tac ltac:(clear - HV103l HV103r K80l K80r) | exactA K79]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV103l HV103r K80l K80r) | exact (conj K80l K80r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV83l HV83r K78l K78r) | evalEk ZA ltac:(clear - HV115l HV115r K82l K82r) | clear - HV83l HV83r K78l K78r; lia | clear - HV83l HV83r K78l K78r; lia | byte_tac ltac:(clear - HV115l HV115r K82l K82r) | exactA K81]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV115l HV115r K82l K82r) | exact (conj K82l K82r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV83l HV83r K78l K78r) | evalEk ZA ltac:(clear) | clear - HV83l HV83r K78l K78r; lia | clear - HV83l HV83r K78l K78r; lia | clear - HV83l HV83r K78l K78r; lia | exactA K83]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K14 K26 K27 K38) | evalEk ZA ltac:(clear - HV82l HV82r K72l K72r) | clear - HV2l HV2r K3l K3r K14 K26 K27 K38; lia | clear - HV2l HV2r K3l K3r K14 K26 K27 K38; lia | exactA K84]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K14 K26 K27 K38) | evalEk ZA ltac:(clear - HV83l HV83r K78l K78r) | clear - HV2l HV2r K3l K3r K14 K26 K27 K38; lia | clear - HV2l HV2r K3l K3r K14 K26 K27 K38; lia | exactA K85]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvO3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvO3.NX0 with 130%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_57 + 0) <= bv_unsigned a < (vz_57 + 0) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PawvO3.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42) | evalEk' ZA Hag ltac:(clear) | clear - HV57l HV57r K34l K34r K36 K38 K39 K40 K41 K42 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvO3.ps0) with 0xafc24 in Hms. change (SR.ps_regs PawvO3.ps0) with (map (fun i => (i, nth i PawvO3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvO3.ps0) with PawvO3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvO3.regs0 PawvO3.regs_out0 130 KS_awvO3 KS_awvO3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvO3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvO3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvO3.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PawvO3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvO3.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PawvO3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvO3.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PawvO3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PawvO3.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PawvO3.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvO4 := LibSegBa_awvO4.
Definition KS_awvO4 : list nat := Eval vm_compute in (BG.kept_list 130 PawvO4.regs0 PawvO4.regs_out0).
Lemma KS_awvO4_ok : BG.kept_ok 130 PawvO4.regs0 PawvO4.regs_out0 KS_awvO4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvO4_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 80%nat) < 2 ^ 64 -> 0 <= (V 81%nat) < 2 ^ 64 -> 0 <= (V 84%nat) < 2 ^ 64 -> 0 <= (V 85%nat) < 2 ^ 64 -> 0 <= (V 86%nat) < 2 ^ 64 -> 0 <= (V 87%nat) < 2 ^ 64 -> 0 <= (V 104%nat) < 2 ^ 64 -> 0 <= (V 105%nat) < 2 ^ 64 -> 0 <= (V 106%nat) < 2 ^ 64 -> 0 <= (V 107%nat) < 2 ^ 64 -> 0 <= (V 116%nat) < 2 ^ 64 -> 0 <= (V 117%nat) < 2 ^ 64 -> 0 <= (V 118%nat) < 2 ^ 64 -> 0 <= (V 119%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 224) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 224) -> getr R (reg 10) = Z_to_bv 64 (V 57%nat) -> getr R (reg 17) = Z_to_bv 64 145760 -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 33%nat) + 368) -> getr R (reg 24) = Z_to_bv 64 (V 36%nat) -> getr R (reg 25) = Z_to_bv 64 (V 81%nat) -> getr R (reg 26) = Z_to_bv 64 (V 80%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1269760 -> L5.u64_at RSEGS M 1300408 2147450880 -> L5.u32_at RSEGS M 1300416 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 224) 224 -> 6897664 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M ((((V 33%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 400) / 8) + 2147450880) 1 ->
  (((V 2%nat) - 224) + 224 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 224)) -> 6897664 <= (V 50%nat) <= 140737488354816 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 512 ->
  L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 50%nat) + 504) (V 51%nat) ->
  4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 512 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) ->
  (((V 2%nat) - 224) + 224 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 224)) -> (((V 2%nat) - 224) + 224 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 224)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 512 <= (V 33%nat)) -> ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) ->
  ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= (((V 33%nat) / 8) + 2147450880)) -> (65536 + 6832128 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) -> (65536 + 6832128 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= 65536) -> (65536 + 6832128 <= (V 51%nat) \/ (V 51%nat) + 1 <= 65536) ->
  4096 <= (V 57%nat) <= 140737488355296 -> aligned (V 57%nat) 8 -> (2147446784 + 17592186048512 <= (V 57%nat) \/ (V 57%nat) + 24 <= 2147446784) -> L5.writable RSEGS M (V 57%nat) 24 ->
  (((V 2%nat) - 224) + 224 <= (V 57%nat) \/ (V 57%nat) + 24 <= ((V 2%nat) - 224)) -> ((V 57%nat) + 24 <= (V 33%nat) \/ (V 33%nat) + 416 <= (V 57%nat)) -> (65536 + 6832128 <= (V 57%nat) \/ (V 57%nat) + 24 <= 65536) -> ((V 57%nat) + 24 <= (V 50%nat) \/ (V 50%nat) + 512 <= (V 57%nat)) ->
  ((V 57%nat) + 24 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 57%nat)) -> L5KA.zeros_at M (((V 57%nat) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 57%nat) + 2) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 57%nat) + 4) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 57%nat) + 6) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 57%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 57%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 57%nat) + 12) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 57%nat) + 14) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 57%nat) + 16) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 57%nat) + 18) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 57%nat) + 20) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 57%nat) + 22) / 8) + 2147450880) 1 -> 0 <= (V 84%nat) <= 255 -> L5.u8_at RSEGS M ((2 * (V 84%nat)) + 145760) (V 104%nat) -> 0 <= (V 104%nat) <= 255 ->
  L5.u8_at RSEGS M ((2 * (V 84%nat)) + 145761) (V 116%nat) -> 0 <= (V 116%nat) <= 255 -> L5KA.zeros_at M ((((2 * (V 84%nat)) + 145760) / 8) + 2147450880) 1 -> 0 <= (V 85%nat) <= 255 ->
  L5.u8_at RSEGS M ((2 * (V 85%nat)) + 145760) (V 105%nat) -> 0 <= (V 105%nat) <= 255 -> L5.u8_at RSEGS M ((2 * (V 85%nat)) + 145761) (V 117%nat) -> 0 <= (V 117%nat) <= 255 ->
  L5KA.zeros_at M ((((2 * (V 85%nat)) + 145760) / 8) + 2147450880) 1 -> 0 <= (V 86%nat) <= 255 -> L5.u8_at RSEGS M ((2 * (V 86%nat)) + 145760) (V 106%nat) -> 0 <= (V 106%nat) <= 255 ->
  L5.u8_at RSEGS M ((2 * (V 86%nat)) + 145761) (V 118%nat) -> 0 <= (V 118%nat) <= 255 -> L5KA.zeros_at M ((((2 * (V 86%nat)) + 145760) / 8) + 2147450880) 1 -> 0 <= (V 87%nat) <= 255 ->
  L5.u8_at RSEGS M ((2 * (V 87%nat)) + 145760) (V 107%nat) -> 0 <= (V 107%nat) <= 255 -> L5.u8_at RSEGS M ((2 * (V 87%nat)) + 145761) (V 119%nat) -> 0 <= (V 119%nat) <= 255 ->
  L5KA.zeros_at M ((((2 * (V 87%nat)) + 145760) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 84%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 184) (V 85%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 176) (V 86%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 168) (V 87%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 57%nat) + 8) <= bv_unsigned a < ((V 57%nat) + 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 57%nat) + 8) <= i < ((V 57%nat) + 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xafc24 M) (st fx' R' 0xafd04 M')
        /\ (forall x, In x KS_awvO4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 57%nat) + 14)
        /\ getr R' (reg 15) = Z_to_bv 64 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 pvzI20 pvzI21 G2 G8 G9 G10 G17 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI22 K4 K5 pvzI23 K7 K8 K9 K10 K11 K12 pvzI24 K14 K15 K16 K17 K18 K19 pvzI25 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 pvzI26 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 pvzI27 K54 pvzI28 K56 pvzI29 K58 pvzI30 K60 pvzI31 K62 pvzI32 K64 pvzI33 K66 pvzI34 K68 pvzI35 K70 pvzI36 K72 pvzI37 K74 pvzI38 K76 K77 K78 K79 K80.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV57l; move HV57l before pvzI7; pose proof (proj2 pvzI7) as HV57r; move HV57r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV80l; move HV80l before pvzI8; pose proof (proj2 pvzI8) as HV80r; move HV80r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV81l; move HV81l before pvzI9; pose proof (proj2 pvzI9) as HV81r; move HV81r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV84l; move HV84l before pvzI10; pose proof (proj2 pvzI10) as HV84r; move HV84r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV85l; move HV85l before pvzI11; pose proof (proj2 pvzI11) as HV85r; move HV85r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV86l; move HV86l before pvzI12; pose proof (proj2 pvzI12) as HV86r; move HV86r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV87l; move HV87l before pvzI13; pose proof (proj2 pvzI13) as HV87r; move HV87r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV104l; move HV104l before pvzI14; pose proof (proj2 pvzI14) as HV104r; move HV104r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV105l; move HV105l before pvzI15; pose proof (proj2 pvzI15) as HV105r; move HV105r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV106l; move HV106l before pvzI16; pose proof (proj2 pvzI16) as HV106r; move HV106r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV107l; move HV107l before pvzI17; pose proof (proj2 pvzI17) as HV107r; move HV107r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV116l; move HV116l before pvzI18; pose proof (proj2 pvzI18) as HV116r; move HV116r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV117l; move HV117l before pvzI19; pose proof (proj2 pvzI19) as HV117r; move HV117r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as HV118l; move HV118l before pvzI20; pose proof (proj2 pvzI20) as HV118r; move HV118r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as HV119l; move HV119l before pvzI21; pose proof (proj2 pvzI21) as HV119r; move HV119r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K3l; move K3l before pvzI22; pose proof (proj2 pvzI22) as K3r; move K3r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K6l; move K6l before pvzI23; pose proof (proj2 pvzI23) as K6r; move K6r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K13l; move K13l before pvzI24; pose proof (proj2 pvzI24) as K13r; move K13r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K20l; move K20l before pvzI25; pose proof (proj2 pvzI25) as K20r; move K20r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K32l; move K32l before pvzI26; pose proof (proj2 pvzI26) as K32r; move K32r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as K53l; move K53l before pvzI27; pose proof (proj2 pvzI27) as K53r; move K53r before pvzI27; clear pvzI27. pose proof (proj1 pvzI28) as K55l; move K55l before pvzI28; pose proof (proj2 pvzI28) as K55r; move K55r before pvzI28; clear pvzI28. pose proof (proj1 pvzI29) as K57l; move K57l before pvzI29; pose proof (proj2 pvzI29) as K57r; move K57r before pvzI29; clear pvzI29. pose proof (proj1 pvzI30) as K59l; move K59l before pvzI30; pose proof (proj2 pvzI30) as K59r; move K59r before pvzI30; clear pvzI30. pose proof (proj1 pvzI31) as K61l; move K61l before pvzI31; pose proof (proj2 pvzI31) as K61r; move K61r before pvzI31; clear pvzI31. pose proof (proj1 pvzI32) as K63l; move K63l before pvzI32; pose proof (proj2 pvzI32) as K63r; move K63r before pvzI32; clear pvzI32. pose proof (proj1 pvzI33) as K65l; move K65l before pvzI33; pose proof (proj2 pvzI33) as K65r; move K65r before pvzI33; clear pvzI33. pose proof (proj1 pvzI34) as K67l; move K67l before pvzI34; pose proof (proj2 pvzI34) as K67r; move K67r before pvzI34; clear pvzI34. pose proof (proj1 pvzI35) as K69l; move K69l before pvzI35; pose proof (proj2 pvzI35) as K69r; move K69r before pvzI35; clear pvzI35. pose proof (proj1 pvzI36) as K71l; move K71l before pvzI36; pose proof (proj2 pvzI36) as K71r; move K71r before pvzI36; clear pvzI36. pose proof (proj1 pvzI37) as K73l; move K73l before pvzI37; pose proof (proj2 pvzI37) as K73r; move K73r before pvzI37; clear pvzI37. pose proof (proj1 pvzI38) as K75l; move K75l before pvzI38; pose proof (proj2 pvzI38) as K75r; move K75r before pvzI38; clear pvzI38.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_80 := V 80%nat) in *. set (vz_81 := V 81%nat) in *. set (vz_84 := V 84%nat) in *. set (vz_85 := V 85%nat) in *. set (vz_86 := V 86%nat) in *. set (vz_87 := V 87%nat) in *. set (vz_104 := V 104%nat) in *. set (vz_105 := V 105%nat) in *. set (vz_106 := V 106%nat) in *. set (vz_107 := V 107%nat) in *. set (vz_116 := V 116%nat) in *. set (vz_117 := V 117%nat) in *. set (vz_118 := V 118%nat) in *. set (vz_119 := V 119%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 57%nat => Z_to_bv 64 vz_57 | 80%nat => Z_to_bv 64 vz_80 | 81%nat => Z_to_bv 64 vz_81 | 84%nat => Z_to_bv 64 vz_84 | 85%nat => Z_to_bv 64 vz_85 | 86%nat => Z_to_bv 64 vz_86 | 87%nat => Z_to_bv 64 vz_87 | 104%nat => Z_to_bv 64 vz_104 | 105%nat => Z_to_bv 64 vz_105 | 106%nat => Z_to_bv 64 vz_106 | 107%nat => Z_to_bv 64 vz_107 | 116%nat => Z_to_bv 64 vz_116 | 117%nat => Z_to_bv 64 vz_117 | 118%nat => Z_to_bv 64 vz_118 | 119%nat => Z_to_bv 64 vz_119 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | 57%nat => vz_57 | 80%nat => vz_80 | 81%nat => vz_81 | 84%nat => vz_84 | 85%nat => vz_85 | 86%nat => vz_86 | 87%nat => vz_87 | 104%nat => vz_104 | 105%nat => vz_105 | 106%nat => vz_106 | 107%nat => vz_107 | 116%nat => vz_116 | 117%nat => vz_117 | 118%nat => vz_118 | 119%nat => vz_119 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 120%nat. }
  assert (HR: regs_ok E PawvO4.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvO4.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvO4.kn0).
  { unfold know_ok, PawvO4.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39) | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K40) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K40) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K40) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K40; lia | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K40; lia | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K40; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K40) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K40) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K40) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K40) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K40) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40) | exact (conj K32l K32r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40) | clear; lia | exact K33]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K40) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | exactA K41]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | exactA K42]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | exactA K43]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | exactA K44]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | exactA K45]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | exactA K46]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | exactA K47]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | exactA K48]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | exactA K49]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | exactA K50]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | exactA K51]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV84l HV84r K53l K53r) | exact (conj K53l K53r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV84l HV84r K53l K53r) | evalEk ZA ltac:(clear - HV104l HV104r K55l K55r) | clear - HV84l HV84r K53l K53r; lia | clear - HV84l HV84r K53l K53r; lia | byte_tac ltac:(clear - HV104l HV104r K55l K55r) | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV104l HV104r K55l K55r) | exact (conj K55l K55r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV84l HV84r K53l K53r) | evalEk ZA ltac:(clear - HV116l HV116r K57l K57r) | clear - HV84l HV84r K53l K53r; lia | clear - HV84l HV84r K53l K53r; lia | byte_tac ltac:(clear - HV116l HV116r K57l K57r) | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV116l HV116r K57l K57r) | exact (conj K57l K57r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV84l HV84r K53l K53r) | evalEk ZA ltac:(clear) | clear - HV84l HV84r K53l K53r; lia | clear - HV84l HV84r K53l K53r; lia | clear - HV84l HV84r K53l K53r; lia | exactA K58]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV85l HV85r K59l K59r) | exact (conj K59l K59r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV85l HV85r K59l K59r) | evalEk ZA ltac:(clear - HV105l HV105r K61l K61r) | clear - HV85l HV85r K59l K59r; lia | clear - HV85l HV85r K59l K59r; lia | byte_tac ltac:(clear - HV105l HV105r K61l K61r) | exactA K60]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV105l HV105r K61l K61r) | exact (conj K61l K61r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV85l HV85r K59l K59r) | evalEk ZA ltac:(clear - HV117l HV117r K63l K63r) | clear - HV85l HV85r K59l K59r; lia | clear - HV85l HV85r K59l K59r; lia | byte_tac ltac:(clear - HV117l HV117r K63l K63r) | exactA K62]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV117l HV117r K63l K63r) | exact (conj K63l K63r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV85l HV85r K59l K59r) | evalEk ZA ltac:(clear) | clear - HV85l HV85r K59l K59r; lia | clear - HV85l HV85r K59l K59r; lia | clear - HV85l HV85r K59l K59r; lia | exactA K64]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV86l HV86r K65l K65r) | exact (conj K65l K65r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV86l HV86r K65l K65r) | evalEk ZA ltac:(clear - HV106l HV106r K67l K67r) | clear - HV86l HV86r K65l K65r; lia | clear - HV86l HV86r K65l K65r; lia | byte_tac ltac:(clear - HV106l HV106r K67l K67r) | exactA K66]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV106l HV106r K67l K67r) | exact (conj K67l K67r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV86l HV86r K65l K65r) | evalEk ZA ltac:(clear - HV118l HV118r K69l K69r) | clear - HV86l HV86r K65l K65r; lia | clear - HV86l HV86r K65l K65r; lia | byte_tac ltac:(clear - HV118l HV118r K69l K69r) | exactA K68]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV118l HV118r K69l K69r) | exact (conj K69l K69r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV86l HV86r K65l K65r) | evalEk ZA ltac:(clear) | clear - HV86l HV86r K65l K65r; lia | clear - HV86l HV86r K65l K65r; lia | clear - HV86l HV86r K65l K65r; lia | exactA K70]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV87l HV87r K71l K71r) | exact (conj K71l K71r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV87l HV87r K71l K71r) | evalEk ZA ltac:(clear - HV107l HV107r K73l K73r) | clear - HV87l HV87r K71l K71r; lia | clear - HV87l HV87r K71l K71r; lia | byte_tac ltac:(clear - HV107l HV107r K73l K73r) | exactA K72]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV107l HV107r K73l K73r) | exact (conj K73l K73r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV87l HV87r K71l K71r) | evalEk ZA ltac:(clear - HV119l HV119r K75l K75r) | clear - HV87l HV87r K71l K71r; lia | clear - HV87l HV87r K71l K71r; lia | byte_tac ltac:(clear - HV119l HV119r K75l K75r) | exactA K74]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV119l HV119r K75l K75r) | exact (conj K75l K75r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV87l HV87r K71l K71r) | evalEk ZA ltac:(clear) | clear - HV87l HV87r K71l K71r; lia | clear - HV87l HV87r K71l K71r; lia | clear - HV87l HV87r K71l K71r; lia | exactA K76]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K36) | evalEk ZA ltac:(clear - HV84l HV84r K53l K53r) | clear - HV2l HV2r K3l K3r K12 K24 K25 K36; lia | clear - HV2l HV2r K3l K3r K12 K24 K25 K36; lia | exactA K77]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K36) | evalEk ZA ltac:(clear - HV85l HV85r K59l K59r) | clear - HV2l HV2r K3l K3r K12 K24 K25 K36; lia | clear - HV2l HV2r K3l K3r K12 K24 K25 K36; lia | exactA K78]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K36) | evalEk ZA ltac:(clear - HV86l HV86r K65l K65r) | clear - HV2l HV2r K3l K3r K12 K24 K25 K36; lia | clear - HV2l HV2r K3l K3r K12 K24 K25 K36; lia | exactA K79]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K36) | evalEk ZA ltac:(clear - HV87l HV87r K71l K71r) | clear - HV2l HV2r K3l K3r K12 K24 K25 K36; lia | clear - HV2l HV2r K3l K3r K12 K24 K25 K36; lia | exactA K80]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvO4.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvO4.NX0 with 130%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_57 + 8) <= bv_unsigned a < (vz_57 + 8) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PawvO4.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40) | evalEk' ZA Hag ltac:(clear) | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvO4.ps0) with 0xafd04 in Hms. change (SR.ps_regs PawvO4.ps0) with (map (fun i => (i, nth i PawvO4.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvO4.ps0) with PawvO4.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvO4.regs0 PawvO4.regs_out0 130 KS_awvO4 KS_awvO4_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvO4.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PawvO4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PawvO4.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PawvO4.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvO5 := LibSegBa_awvO5.
Definition KS_awvO5 : list nat := Eval vm_compute in (BG.kept_list 130 PawvO5.regs0 PawvO5.regs_out0).
Lemma KS_awvO5_ok : BG.kept_ok 130 PawvO5.regs0 PawvO5.regs_out0 KS_awvO5 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvO5_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 80%nat) < 2 ^ 64 -> 0 <= (V 81%nat) < 2 ^ 64 -> 0 <= (V 88%nat) < 2 ^ 64 -> 0 <= (V 89%nat) < 2 ^ 64 -> 0 <= (V 90%nat) < 2 ^ 64 -> 0 <= (V 91%nat) < 2 ^ 64 -> 0 <= (V 108%nat) < 2 ^ 64 -> 0 <= (V 109%nat) < 2 ^ 64 -> 0 <= (V 110%nat) < 2 ^ 64 -> 0 <= (V 111%nat) < 2 ^ 64 -> 0 <= (V 120%nat) < 2 ^ 64 -> 0 <= (V 121%nat) < 2 ^ 64 -> 0 <= (V 122%nat) < 2 ^ 64 -> 0 <= (V 123%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 224) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 224) -> getr R (reg 10) = Z_to_bv 64 (V 57%nat) -> getr R (reg 17) = Z_to_bv 64 145760 -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 33%nat) + 368) -> getr R (reg 24) = Z_to_bv 64 (V 36%nat) -> getr R (reg 25) = Z_to_bv 64 (V 81%nat) -> getr R (reg 26) = Z_to_bv 64 (V 80%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1269760 -> L5.u64_at RSEGS M 1300408 2147450880 -> L5.u32_at RSEGS M 1300416 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 224) 224 -> 6897664 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M ((((V 33%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 400) / 8) + 2147450880) 1 ->
  (((V 2%nat) - 224) + 224 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 224)) -> 6897664 <= (V 50%nat) <= 140737488354816 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 512 ->
  L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 50%nat) + 504) (V 51%nat) ->
  4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 512 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) ->
  (((V 2%nat) - 224) + 224 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 224)) -> (((V 2%nat) - 224) + 224 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 224)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 512 <= (V 33%nat)) -> ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) ->
  ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= (((V 33%nat) / 8) + 2147450880)) -> (65536 + 6832128 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) -> (65536 + 6832128 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= 65536) -> (65536 + 6832128 <= (V 51%nat) \/ (V 51%nat) + 1 <= 65536) ->
  4096 <= (V 57%nat) <= 140737488355296 -> aligned (V 57%nat) 8 -> (2147446784 + 17592186048512 <= (V 57%nat) \/ (V 57%nat) + 24 <= 2147446784) -> L5.writable RSEGS M (V 57%nat) 24 ->
  (((V 2%nat) - 224) + 224 <= (V 57%nat) \/ (V 57%nat) + 24 <= ((V 2%nat) - 224)) -> ((V 57%nat) + 24 <= (V 33%nat) \/ (V 33%nat) + 416 <= (V 57%nat)) -> (65536 + 6832128 <= (V 57%nat) \/ (V 57%nat) + 24 <= 65536) -> ((V 57%nat) + 24 <= (V 50%nat) \/ (V 50%nat) + 512 <= (V 57%nat)) ->
  ((V 57%nat) + 24 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 57%nat)) -> L5KA.zeros_at M (((V 57%nat) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 57%nat) + 2) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 57%nat) + 4) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 57%nat) + 6) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 57%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 57%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 57%nat) + 12) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 57%nat) + 14) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 57%nat) + 16) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 57%nat) + 18) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 57%nat) + 20) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 57%nat) + 22) / 8) + 2147450880) 1 -> 0 <= (V 88%nat) <= 255 -> L5.u8_at RSEGS M ((2 * (V 88%nat)) + 145760) (V 108%nat) -> 0 <= (V 108%nat) <= 255 ->
  L5.u8_at RSEGS M ((2 * (V 88%nat)) + 145761) (V 120%nat) -> 0 <= (V 120%nat) <= 255 -> L5KA.zeros_at M ((((2 * (V 88%nat)) + 145760) / 8) + 2147450880) 1 -> 0 <= (V 89%nat) <= 255 ->
  L5.u8_at RSEGS M ((2 * (V 89%nat)) + 145760) (V 109%nat) -> 0 <= (V 109%nat) <= 255 -> L5.u8_at RSEGS M ((2 * (V 89%nat)) + 145761) (V 121%nat) -> 0 <= (V 121%nat) <= 255 ->
  L5KA.zeros_at M ((((2 * (V 89%nat)) + 145760) / 8) + 2147450880) 1 -> 0 <= (V 90%nat) <= 255 -> L5.u8_at RSEGS M ((2 * (V 90%nat)) + 145760) (V 110%nat) -> 0 <= (V 110%nat) <= 255 ->
  L5.u8_at RSEGS M ((2 * (V 90%nat)) + 145761) (V 122%nat) -> 0 <= (V 122%nat) <= 255 -> L5KA.zeros_at M ((((2 * (V 90%nat)) + 145760) / 8) + 2147450880) 1 -> 0 <= (V 91%nat) <= 255 ->
  L5.u8_at RSEGS M ((2 * (V 91%nat)) + 145760) (V 111%nat) -> 0 <= (V 111%nat) <= 255 -> L5.u8_at RSEGS M ((2 * (V 91%nat)) + 145761) (V 123%nat) -> 0 <= (V 123%nat) <= 255 ->
  L5KA.zeros_at M ((((2 * (V 91%nat)) + 145760) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 88%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 89%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 90%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) (V 91%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 57%nat) + 16) <= bv_unsigned a < ((V 57%nat) + 16) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 57%nat) + 16) <= i < ((V 57%nat) + 16) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xafd04 M) (st fx' R' 0xafde4 M')
        /\ (forall x, In x KS_awvO5 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 57%nat) + 22)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 15) = Z_to_bv 64 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 pvzI20 pvzI21 G2 G8 G9 G10 G17 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI22 K4 K5 pvzI23 K7 K8 K9 K10 K11 K12 pvzI24 K14 K15 K16 K17 K18 K19 pvzI25 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 pvzI26 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 pvzI27 K54 pvzI28 K56 pvzI29 K58 pvzI30 K60 pvzI31 K62 pvzI32 K64 pvzI33 K66 pvzI34 K68 pvzI35 K70 pvzI36 K72 pvzI37 K74 pvzI38 K76 K77 K78 K79 K80.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV57l; move HV57l before pvzI7; pose proof (proj2 pvzI7) as HV57r; move HV57r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV80l; move HV80l before pvzI8; pose proof (proj2 pvzI8) as HV80r; move HV80r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV81l; move HV81l before pvzI9; pose proof (proj2 pvzI9) as HV81r; move HV81r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV88l; move HV88l before pvzI10; pose proof (proj2 pvzI10) as HV88r; move HV88r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV89l; move HV89l before pvzI11; pose proof (proj2 pvzI11) as HV89r; move HV89r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV90l; move HV90l before pvzI12; pose proof (proj2 pvzI12) as HV90r; move HV90r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV91l; move HV91l before pvzI13; pose proof (proj2 pvzI13) as HV91r; move HV91r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV108l; move HV108l before pvzI14; pose proof (proj2 pvzI14) as HV108r; move HV108r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV109l; move HV109l before pvzI15; pose proof (proj2 pvzI15) as HV109r; move HV109r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV110l; move HV110l before pvzI16; pose proof (proj2 pvzI16) as HV110r; move HV110r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV111l; move HV111l before pvzI17; pose proof (proj2 pvzI17) as HV111r; move HV111r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV120l; move HV120l before pvzI18; pose proof (proj2 pvzI18) as HV120r; move HV120r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV121l; move HV121l before pvzI19; pose proof (proj2 pvzI19) as HV121r; move HV121r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as HV122l; move HV122l before pvzI20; pose proof (proj2 pvzI20) as HV122r; move HV122r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as HV123l; move HV123l before pvzI21; pose proof (proj2 pvzI21) as HV123r; move HV123r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K3l; move K3l before pvzI22; pose proof (proj2 pvzI22) as K3r; move K3r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K6l; move K6l before pvzI23; pose proof (proj2 pvzI23) as K6r; move K6r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K13l; move K13l before pvzI24; pose proof (proj2 pvzI24) as K13r; move K13r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K20l; move K20l before pvzI25; pose proof (proj2 pvzI25) as K20r; move K20r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K32l; move K32l before pvzI26; pose proof (proj2 pvzI26) as K32r; move K32r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as K53l; move K53l before pvzI27; pose proof (proj2 pvzI27) as K53r; move K53r before pvzI27; clear pvzI27. pose proof (proj1 pvzI28) as K55l; move K55l before pvzI28; pose proof (proj2 pvzI28) as K55r; move K55r before pvzI28; clear pvzI28. pose proof (proj1 pvzI29) as K57l; move K57l before pvzI29; pose proof (proj2 pvzI29) as K57r; move K57r before pvzI29; clear pvzI29. pose proof (proj1 pvzI30) as K59l; move K59l before pvzI30; pose proof (proj2 pvzI30) as K59r; move K59r before pvzI30; clear pvzI30. pose proof (proj1 pvzI31) as K61l; move K61l before pvzI31; pose proof (proj2 pvzI31) as K61r; move K61r before pvzI31; clear pvzI31. pose proof (proj1 pvzI32) as K63l; move K63l before pvzI32; pose proof (proj2 pvzI32) as K63r; move K63r before pvzI32; clear pvzI32. pose proof (proj1 pvzI33) as K65l; move K65l before pvzI33; pose proof (proj2 pvzI33) as K65r; move K65r before pvzI33; clear pvzI33. pose proof (proj1 pvzI34) as K67l; move K67l before pvzI34; pose proof (proj2 pvzI34) as K67r; move K67r before pvzI34; clear pvzI34. pose proof (proj1 pvzI35) as K69l; move K69l before pvzI35; pose proof (proj2 pvzI35) as K69r; move K69r before pvzI35; clear pvzI35. pose proof (proj1 pvzI36) as K71l; move K71l before pvzI36; pose proof (proj2 pvzI36) as K71r; move K71r before pvzI36; clear pvzI36. pose proof (proj1 pvzI37) as K73l; move K73l before pvzI37; pose proof (proj2 pvzI37) as K73r; move K73r before pvzI37; clear pvzI37. pose proof (proj1 pvzI38) as K75l; move K75l before pvzI38; pose proof (proj2 pvzI38) as K75r; move K75r before pvzI38; clear pvzI38.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_80 := V 80%nat) in *. set (vz_81 := V 81%nat) in *. set (vz_88 := V 88%nat) in *. set (vz_89 := V 89%nat) in *. set (vz_90 := V 90%nat) in *. set (vz_91 := V 91%nat) in *. set (vz_108 := V 108%nat) in *. set (vz_109 := V 109%nat) in *. set (vz_110 := V 110%nat) in *. set (vz_111 := V 111%nat) in *. set (vz_120 := V 120%nat) in *. set (vz_121 := V 121%nat) in *. set (vz_122 := V 122%nat) in *. set (vz_123 := V 123%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 57%nat => Z_to_bv 64 vz_57 | 80%nat => Z_to_bv 64 vz_80 | 81%nat => Z_to_bv 64 vz_81 | 88%nat => Z_to_bv 64 vz_88 | 89%nat => Z_to_bv 64 vz_89 | 90%nat => Z_to_bv 64 vz_90 | 91%nat => Z_to_bv 64 vz_91 | 108%nat => Z_to_bv 64 vz_108 | 109%nat => Z_to_bv 64 vz_109 | 110%nat => Z_to_bv 64 vz_110 | 111%nat => Z_to_bv 64 vz_111 | 120%nat => Z_to_bv 64 vz_120 | 121%nat => Z_to_bv 64 vz_121 | 122%nat => Z_to_bv 64 vz_122 | 123%nat => Z_to_bv 64 vz_123 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | 57%nat => vz_57 | 80%nat => vz_80 | 81%nat => vz_81 | 88%nat => vz_88 | 89%nat => vz_89 | 90%nat => vz_90 | 91%nat => vz_91 | 108%nat => vz_108 | 109%nat => vz_109 | 110%nat => vz_110 | 111%nat => vz_111 | 120%nat => vz_120 | 121%nat => vz_121 | 122%nat => vz_122 | 123%nat => vz_123 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 124%nat. }
  assert (HR: regs_ok E PawvO5.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvO5.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvO5.kn0).
  { unfold know_ok, PawvO5.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39) | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K40) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K40) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K40) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K40; lia | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K40; lia | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K40; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K40) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K40) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K40) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K40) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K40) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40) | exact (conj K32l K32r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40) | clear; lia | exact K33]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K39) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K40) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | exactA K41]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | exactA K42]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | exactA K43]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | exactA K44]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | exactA K45]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | exactA K46]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | exactA K47]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | exactA K48]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | exactA K49]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | exactA K50]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | exactA K51]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV88l HV88r K53l K53r) | exact (conj K53l K53r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV88l HV88r K53l K53r) | evalEk ZA ltac:(clear - HV108l HV108r K55l K55r) | clear - HV88l HV88r K53l K53r; lia | clear - HV88l HV88r K53l K53r; lia | byte_tac ltac:(clear - HV108l HV108r K55l K55r) | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV108l HV108r K55l K55r) | exact (conj K55l K55r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV88l HV88r K53l K53r) | evalEk ZA ltac:(clear - HV120l HV120r K57l K57r) | clear - HV88l HV88r K53l K53r; lia | clear - HV88l HV88r K53l K53r; lia | byte_tac ltac:(clear - HV120l HV120r K57l K57r) | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV120l HV120r K57l K57r) | exact (conj K57l K57r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV88l HV88r K53l K53r) | evalEk ZA ltac:(clear) | clear - HV88l HV88r K53l K53r; lia | clear - HV88l HV88r K53l K53r; lia | clear - HV88l HV88r K53l K53r; lia | exactA K58]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV89l HV89r K59l K59r) | exact (conj K59l K59r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV89l HV89r K59l K59r) | evalEk ZA ltac:(clear - HV109l HV109r K61l K61r) | clear - HV89l HV89r K59l K59r; lia | clear - HV89l HV89r K59l K59r; lia | byte_tac ltac:(clear - HV109l HV109r K61l K61r) | exactA K60]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV109l HV109r K61l K61r) | exact (conj K61l K61r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV89l HV89r K59l K59r) | evalEk ZA ltac:(clear - HV121l HV121r K63l K63r) | clear - HV89l HV89r K59l K59r; lia | clear - HV89l HV89r K59l K59r; lia | byte_tac ltac:(clear - HV121l HV121r K63l K63r) | exactA K62]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV121l HV121r K63l K63r) | exact (conj K63l K63r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV89l HV89r K59l K59r) | evalEk ZA ltac:(clear) | clear - HV89l HV89r K59l K59r; lia | clear - HV89l HV89r K59l K59r; lia | clear - HV89l HV89r K59l K59r; lia | exactA K64]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV90l HV90r K65l K65r) | exact (conj K65l K65r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV90l HV90r K65l K65r) | evalEk ZA ltac:(clear - HV110l HV110r K67l K67r) | clear - HV90l HV90r K65l K65r; lia | clear - HV90l HV90r K65l K65r; lia | byte_tac ltac:(clear - HV110l HV110r K67l K67r) | exactA K66]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV110l HV110r K67l K67r) | exact (conj K67l K67r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV90l HV90r K65l K65r) | evalEk ZA ltac:(clear - HV122l HV122r K69l K69r) | clear - HV90l HV90r K65l K65r; lia | clear - HV90l HV90r K65l K65r; lia | byte_tac ltac:(clear - HV122l HV122r K69l K69r) | exactA K68]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV122l HV122r K69l K69r) | exact (conj K69l K69r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV90l HV90r K65l K65r) | evalEk ZA ltac:(clear) | clear - HV90l HV90r K65l K65r; lia | clear - HV90l HV90r K65l K65r; lia | clear - HV90l HV90r K65l K65r; lia | exactA K70]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV91l HV91r K71l K71r) | exact (conj K71l K71r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV91l HV91r K71l K71r) | evalEk ZA ltac:(clear - HV111l HV111r K73l K73r) | clear - HV91l HV91r K71l K71r; lia | clear - HV91l HV91r K71l K71r; lia | byte_tac ltac:(clear - HV111l HV111r K73l K73r) | exactA K72]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV111l HV111r K73l K73r) | exact (conj K73l K73r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV91l HV91r K71l K71r) | evalEk ZA ltac:(clear - HV123l HV123r K75l K75r) | clear - HV91l HV91r K71l K71r; lia | clear - HV91l HV91r K71l K71r; lia | byte_tac ltac:(clear - HV123l HV123r K75l K75r) | exactA K74]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV123l HV123r K75l K75r) | exact (conj K75l K75r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV91l HV91r K71l K71r) | evalEk ZA ltac:(clear) | clear - HV91l HV91r K71l K71r; lia | clear - HV91l HV91r K71l K71r; lia | clear - HV91l HV91r K71l K71r; lia | exactA K76]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K36) | evalEk ZA ltac:(clear - HV88l HV88r K53l K53r) | clear - HV2l HV2r K3l K3r K12 K24 K25 K36; lia | clear - HV2l HV2r K3l K3r K12 K24 K25 K36; lia | exactA K77]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K36) | evalEk ZA ltac:(clear - HV89l HV89r K59l K59r) | clear - HV2l HV2r K3l K3r K12 K24 K25 K36; lia | clear - HV2l HV2r K3l K3r K12 K24 K25 K36; lia | exactA K78]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K36) | evalEk ZA ltac:(clear - HV90l HV90r K65l K65r) | clear - HV2l HV2r K3l K3r K12 K24 K25 K36; lia | clear - HV2l HV2r K3l K3r K12 K24 K25 K36; lia | exactA K79]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K36) | evalEk ZA ltac:(clear - HV91l HV91r K71l K71r) | clear - HV2l HV2r K3l K3r K12 K24 K25 K36; lia | clear - HV2l HV2r K3l K3r K12 K24 K25 K36; lia | exactA K80]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvO5.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvO5.NX0 with 130%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_57 + 16) <= bv_unsigned a < (vz_57 + 16) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PawvO5.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40) | evalEk' ZA Hag ltac:(clear) | clear - HV57l HV57r K32l K32r K34 K36 K37 K38 K39 K40 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvO5.ps0) with 0xafde4 in Hms. change (SR.ps_regs PawvO5.ps0) with (map (fun i => (i, nth i PawvO5.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvO5.ps0) with PawvO5.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvO5.regs0 PawvO5.regs_out0 130 KS_awvO5 KS_awvO5_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvO5.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvO5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvO5.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PawvO5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PawvO5.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PawvO5.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvO6 := LibSegBa_awvO6.
Definition KS_awvO6 : list nat := Eval vm_compute in (BG.kept_list 130 PawvO6.regs0 PawvO6.regs_out0).
Lemma KS_awvO6_ok : BG.kept_ok 130 PawvO6.regs0 PawvO6.regs_out0 KS_awvO6 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvO6_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 224) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 224) -> getr R (reg 13) = Z_to_bv 64 ((((V 33%nat) + 368) / 8) + 2147450880) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 33%nat) + 368) -> getr R (reg 24) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1269760 -> L5.u64_at RSEGS M 1300408 2147450880 -> L5.u32_at RSEGS M 1300416 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 224) 224 -> 6897664 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M ((((V 33%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 400) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 368) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 384) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 376) / 8) + 2147450880) 1 -> (((V 2%nat) - 224) + 224 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 224)) ->
  6897664 <= (V 50%nat) <= 140737488354816 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 512 -> L5.writable RSEGS M (V 50%nat) 512 ->
  (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 50%nat) + 504) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 ->
  L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 512 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 224) + 224 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 224)) ->
  (((V 2%nat) - 224) + 224 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 224)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 512 <= (V 33%nat)) -> ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= (((V 33%nat) / 8) + 2147450880)) ->
  (65536 + 6832128 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) -> (65536 + 6832128 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= 65536) -> (65536 + 6832128 <= (V 51%nat) \/ (V 51%nat) + 1 <= 65536) -> 6897664 <= (V 34%nat) <= 140737488355320 ->
  aligned (V 34%nat) 8 -> (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 -> (((V 2%nat) - 224) + 224 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 2%nat) - 224)) ->
  ((V 33%nat) + 416 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 33%nat)) -> ((V 50%nat) + 512 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 50%nat)) -> ((V 51%nat) + 1 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 51%nat)) -> L5.u64_at RSEGS M (V 34%nat) 1241824 ->
  L5KA.zeros_at M 2147606123 1 -> ((((V 34%nat) / 8) + 2147450880) + 1 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= (((V 34%nat) / 8) + 2147450880)) -> 4096 <= (V 57%nat) <= 140737488355296 -> aligned (V 57%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 57%nat) \/ (V 57%nat) + 24 <= 2147446784) -> L5.writable RSEGS M (V 57%nat) 24 -> (((V 2%nat) - 224) + 224 <= (V 57%nat) \/ (V 57%nat) + 24 <= ((V 2%nat) - 224)) -> ((V 57%nat) + 24 <= (V 33%nat) \/ (V 33%nat) + 416 <= (V 57%nat)) ->
  (65536 + 6832128 <= (V 57%nat) \/ (V 57%nat) + 24 <= 65536) -> ((V 57%nat) + 24 <= (V 50%nat) \/ (V 50%nat) + 512 <= (V 57%nat)) -> ((V 57%nat) + 24 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 57%nat)) -> L5KA.zeros_at M (((V 57%nat) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 57%nat) + 2) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 57%nat) + 4) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 57%nat) + 6) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 57%nat) + 8) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 57%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 57%nat) + 12) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 57%nat) + 14) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 57%nat) + 16) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 57%nat) + 18) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 57%nat) + 20) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 57%nat) + 22) / 8) + 2147450880) 1 -> L5.u8_at RSEGS M ((V 33%nat) + 368) (V 56%nat) ->
  0 <= (V 56%nat) <= 255 -> Z.testbit (V 56%nat) 0 = true -> L5.u64_at RSEGS M ((V 33%nat) + 384) (V 57%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 376) (V 58%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((((V 50%nat) / 8) + 2147450880) + 56) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 56) + 2) -> ~ (((V 50%nat) + 448) <= bv_unsigned a < ((V 50%nat) + 448) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((((V 50%nat) / 8) + 2147450880) + 56) <= i < ((((V 50%nat) / 8) + 2147450880) + 56) + 2) -> ~ (((V 50%nat) + 448) <= i < ((V 50%nat) + 448) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xafde4 M) (st fx' R' 0xafe88 M')
        /\ (forall x, In x KS_awvO6 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 720520
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 50%nat) + 448)
        /\ getr R' (reg 12) = Z_to_bv 64 19
        /\ getr R' (reg 13) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 691824
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 456) (V 58%nat)
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 448) (V 57%nat)
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450937) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450936) 0
        /\ L5.defined M' (V 50%nat) 448
        /\ L5.defined M' ((V 50%nat) + 464) 48).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G8 G9 G13 G18 G19 G20 G21 G22 G23 G24 G27 K0 K1 K2 pvzI10 K4 K5 pvzI11 K7 K8 K9 K10 K11 K12 K13 K14 K15 pvzI12 K17 K18 K19 K20 K21 K22 pvzI13 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 pvzI14 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 pvzI15 K47 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57 K58 K59 K60 K61 K62 K63 K64 K65 K66 K67 pvzI16 K69 K70 K71.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV56l; move HV56l before pvzI7; pose proof (proj2 pvzI7) as HV56r; move HV56r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV57l; move HV57l before pvzI8; pose proof (proj2 pvzI8) as HV57r; move HV57r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV58l; move HV58l before pvzI9; pose proof (proj2 pvzI9) as HV58r; move HV58r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K6l; move K6l before pvzI11; pose proof (proj2 pvzI11) as K6r; move K6r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K16l; move K16l before pvzI12; pose proof (proj2 pvzI12) as K16r; move K16r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K23l; move K23l before pvzI13; pose proof (proj2 pvzI13) as K23r; move K23r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K35l; move K35l before pvzI14; pose proof (proj2 pvzI14) as K35r; move K35r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K46l; move K46l before pvzI15; pose proof (proj2 pvzI15) as K46r; move K46r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K68l; move K68l before pvzI16; pose proof (proj2 pvzI16) as K68r; move K68r before pvzI16; clear pvzI16.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | 56%nat => vz_56 | 57%nat => vz_57 | 58%nat => vz_58 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 59%nat. }
  assert (HR: regs_ok E PawvO6.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvO6.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvO6.kn0).
  { unfold know_ok, PawvO6.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K15 K27 K28 K39 K50) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K15 K27 K28 K39 K50) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K15 K27 K28 K39 K50) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K15 K27 K28 K39 K50; lia | clear - HV2l HV2r K3l K3r K15 K27 K28 K39 K50; lia | clear - HV2l HV2r K3l K3r K15 K27 K28 K39 K50; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40 K51) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40 K51) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40 K51) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40 K51) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40 K51; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40 K51; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40 K51; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40 K51) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40 K51; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40 K51; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40 K51; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40 K51) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40 K51; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40 K51; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40 K51; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40 K51) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40 K51; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40 K51; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40 K51; lia | exactA K12]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40 K51) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40 K51; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40 K51; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40 K51; lia | exactA K13]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40 K51) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40 K51; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40 K51; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40 K51; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K15 K27 K28 K39 K50) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40 K51) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45 K53) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45 K53) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45 K53) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45 K53; lia | clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45 K53; lia | clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45 K53; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45 K53) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45 K53; lia | clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45 K53; lia | clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45 K53; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45 K53) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45 K53) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45 K53; lia | clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45 K53; lia | clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45 K53; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45 K53) | evalEk ZA ltac:(clear - HV51l HV51r K23l K23r K25 K26 K28 K30 K34 K42 K54) | clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45 K53; lia | clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45 K53; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K23l K23r K25 K26 K28 K30 K34 K42 K54) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K23l K23r K25 K26 K28 K30 K34 K42 K54) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K23l K23r K25 K26 K28 K30 K34 K42 K54; lia | clear - HV51l HV51r K23l K23r K25 K26 K28 K30 K34 K42 K54; lia | clear - HV51l HV51r K23l K23r K25 K26 K28 K30 K34 K42 K54; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K23l K23r K25 K26 K28 K30 K34 K42 K54) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45 K53) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K23l K23r K25 K26 K28 K30 K34 K42 K54) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K15 K27 K28 K39 K50) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45 K53) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K15 K27 K28 K39 K50) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K23l K23r K25 K26 K28 K30 K34 K42 K54) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40 K51) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45 K53) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40 K51) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K23l K23r K25 K26 K28 K30 K34 K42 K54) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40 K51) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45 K53) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45 K53) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45 K53) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K23l K23r K25 K26 K28 K30 K34 K42 K54) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K35l K35r K37 K39 K40 K41 K42 K45) | exact (conj K35l K35r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K35l K35r K37 K39 K40 K41 K42 K45) | clear; lia | exact K36]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K35l K35r K37 K39 K40 K41 K42 K45) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K35l K35r K37 K39 K40 K41 K42 K45) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K35l K35r K37 K39 K40 K41 K42 K45; lia | clear - HV34l HV34r K35l K35r K37 K39 K40 K41 K42 K45; lia | clear - HV34l HV34r K35l K35r K37 K39 K40 K41 K42 K45; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K15 K27 K28 K39 K50) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K35l K35r K37 K39 K40 K41 K42 K45) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40 K51) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K35l K35r K37 K39 K40 K41 K42 K45) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45 K53) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K35l K35r K37 K39 K40 K41 K42 K45) | evalEk ZA ltac:(clear) | generalize K41; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K23l K23r K25 K26 K28 K30 K34 K42 K54) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K35l K35r K37 K39 K40 K41 K42 K45) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K35l K35r K37 K39 K40 K41 K42 K45) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K35l K35r K37 K39 K40 K41 K42 K45; lia | clear - HV34l HV34r K35l K35r K37 K39 K40 K41 K42 K45; lia | exactA K43]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K35l K35r K37 K39 K40 K41 K42 K45) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45 K53) | evalEk ZA ltac:(clear) | generalize K45; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54) | exact (conj K46l K46r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54) | clear; lia | exact K47]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54; lia | clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54; lia | clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54; lia | exactA K49]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K15 K27 K28 K39 K50) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40 K51) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54) | evalEk ZA ltac:(clear) | generalize K52; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45 K53) | evalEk ZA ltac:(clear) | generalize K53; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K23l K23r K25 K26 K28 K30 K34 K42 K54) | evalEk ZA ltac:(clear) | generalize K54; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54; lia | clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54; lia | clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54; lia | exactA K55]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54; lia | clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54; lia | clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54; lia | exactA K56]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54; lia | clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54; lia | clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54; lia | exactA K57]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54; lia | clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54; lia | clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54; lia | exactA K58]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54; lia | clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54; lia | clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54; lia | exactA K59]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54; lia | clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54; lia | clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54; lia | exactA K60]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54; lia | clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54; lia | clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54; lia | exactA K61]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54; lia | clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54; lia | clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54; lia | exactA K62]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54; lia | clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54; lia | clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54; lia | exactA K63]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54; lia | clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54; lia | clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54; lia | exactA K64]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54; lia | clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54; lia | clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54; lia | exactA K65]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54; lia | clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54; lia | clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54; lia | exactA K66]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40 K51) | evalEk ZA ltac:(clear - HV56l HV56r K68l K68r K69) | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40 K51; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40 K51; lia | byte_tac ltac:(clear - HV56l HV56r K68l K68r K69) | exactA K67]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV56l HV56r K68l K68r K69) | exact (conj K68l K68r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV56l HV56r K68l K68r K69) | clear; lia | rewrite (L5K.land1_bit0_true vz_56 ltac:(clear - HV56l HV56r K68l K68r K69; lia) K69); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40 K51) | evalEk ZA ltac:(clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54) | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40 K51; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40 K51; lia | exactA K70]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40 K51) | evalEk ZA ltac:(clear - HV58l HV58r) | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40 K51; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40 K51; lia | exactA K71]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvO6.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvO6.NX0 with 130%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((vz_50 / 8) + 2147450880) + 56) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 56) + 2) -> ~ ((vz_50 + 448) <= bv_unsigned a < (vz_50 + 448) + 16) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PawvO6.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45 K53) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45 K53 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45 K53) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45 K53 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvO6.ps0) with 0xafe88 in Hms. change (SR.ps_regs PawvO6.ps0) with (map (fun i => (i, nth i PawvO6.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvO6.ps0) with PawvO6.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvO6.regs0 PawvO6.regs_out0 130 KS_awvO6 KS_awvO6_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvO6.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PawvO6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvO6.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvO6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvO6.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvO6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvO6.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PawvO6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvO6.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PawvO6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvO6.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PawvO6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvO6.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PawvO6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45 K53) | evalEk' ZA Hag ltac:(clear - HV58l HV58r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45 K53) | evalEk' ZA Hag ltac:(clear - HV57l HV57r K46l K46r K48 K50 K51 K52 K53 K54) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45 K53) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45 K53) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45 K53) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45 K53) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvO7 := LibSegBa_awvO7.
Definition KS_awvO7 : list nat := Eval vm_compute in (BG.kept_list 130 PawvO7.regs0 PawvO7.regs_out0).
Lemma KS_awvO7_ok : BG.kept_ok 130 PawvO7.regs0 PawvO7.regs_out0 KS_awvO7 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvO7_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 224) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 224) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 33%nat) + 368) -> getr R (reg 24) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1269760 -> L5.u64_at RSEGS M 1300408 2147450880 -> L5.u32_at RSEGS M 1300416 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 224) 224 -> 6897664 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M ((((V 33%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 400) / 8) + 2147450880) 1 ->
  (((V 2%nat) - 224) + 224 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 224)) -> 6897664 <= (V 50%nat) <= 140737488354816 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 512 ->
  L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 50%nat) + 504) (V 51%nat) ->
  4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 512 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) ->
  (((V 2%nat) - 224) + 224 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 224)) -> (((V 2%nat) - 224) + 224 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 224)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 512 <= (V 33%nat)) -> ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) ->
  ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= (((V 33%nat) / 8) + 2147450880)) -> (65536 + 6832128 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) -> (65536 + 6832128 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= 65536) -> (65536 + 6832128 <= (V 51%nat) \/ (V 51%nat) + 1 <= 65536) ->
  L5.writable RSEGS M ((V 33%nat) + 8) 1 -> L5.u8_at RSEGS M ((V 33%nat) + 10) 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 64) -> ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 64) -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xafe88 M) (st fx' R' 0x7b544 M')
        /\ (forall x, In x KS_awvO7 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 720824
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880)
        /\ getr R' (reg 11) = Z_to_bv 64 64
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' (V 50%nat) 1172321806
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450933) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450932) 248
        /\ L5.u8_at RSEGS M' ((V 33%nat) + 8) 1
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450937) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450936) 248
        /\ L5.defined M' ((V 50%nat) + 8) 504).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 pvzI9 K14 K15 K16 K17 K18 K19 pvzI10 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K13l; move K13l before pvzI9; pose proof (proj2 pvzI9) as K13r; move K13r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K20l; move K20l before pvzI10; pose proof (proj2 pvzI10) as K20r; move K20r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PawvO7.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvO7.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvO7.kn0).
  { unfold know_ok, PawvO7.kn0.
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
  pvz_hg ltac:(idtac; destruct (PawvO7.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvO7.NX0 with 130%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 8) -> ~ ((((vz_50 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 0) + 64) -> ~ ((vz_33 + 8) <= bv_unsigned a < (vz_33 + 8) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PawvO7.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvO7.ps0) with 0x7b544 in Hms. change (SR.ps_regs PawvO7.ps0) with (map (fun i => (i, nth i PawvO7.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvO7.ps0) with PawvO7.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvO7.regs0 PawvO7.regs_out0 130 KS_awvO7 KS_awvO7_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvO7.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PawvO7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvO7.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvO7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvO7.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvO7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvO7.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PawvO7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

End PNARVOP.
