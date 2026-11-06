(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BigLinkZA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Ja0PlanKit AsanPlanCore
BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan Require Import XIcptA XIcptAs0Kit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJa_ardC LibSegJa_ardD LibSegJa_ardE LibSegJa_ardF LibSegJa_ardG LibSegJa_ardH LibSegJa_ardZ.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMARDP.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
intros A Pz. rewrite (BG.word_of_unsigned (edenot E e) (z mod BL.MM) (L5KA.zpolyA_sound E Vz e z A Pz)).
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, BL.MM. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof. intros K Ha Hv ->. eapply L5K.u64_of_KWord8; eauto. Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof. intros K Ha Hv ->. eapply L5K.u32_of_KWord4; eauto. Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof. intros K Ha Hv Hr ->. eapply L5K.u8_of_KWord1; eauto. Qed.
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
Local Ltac solve_modk k :=
repeat match goal with |- context [(?x mod 18446744073709551616) / _] => rewrite (Z.mod_small x 18446744073709551616) by (k; zfacts; lia) end;
first [ rewrite Z.mod_small; [ first [reflexivity | k; lia] | k; L5K.zrange_tac ]
| symmetry; eapply (Z.mod_unique_pos _ _ (-1)); k; unfold BL.MM; lia
| symmetry; eapply (Z.mod_unique_pos _ _ 1); k; unfold BL.MM; lia ].
Local Ltac pvz_hg tac := lazymatch goal with |- ?G0 => let PG := fresh "PGoal" in set (PG := G0); tac; subst PG end.
Local Ltac pvz_fold B k := lazymatch B with | ?A2 /\ ?B2 => pvz_fold B2 ltac:(fun T2 => let T := fresh "pvzT" in pose (T := A2 /\ T2); k T) | _ => k B end.
Local Ltac pvz_linconj := lazymatch goal with |- ?A /\ ?B => pvz_fold B ltac:(fun T => change_no_check (A /\ T)) | _ => idtac end.
Local Ltac pvz_unfold ZA := lazymatch type of ZA with forall j, _ = ?f j => tryif is_var f then unfold f else idtac | _ => idtac end.
Tactic Notation "evalEk" constr(ZA) tactic(k) :=
L5K.norm_expr; eapply L5KA.zpolyA_val; [ apply (L5K.zagree_all _ _ _ ZA) | cbn [L5KA.zpolyA]; pvz_unfold ZA; reflexivity | solve_modk k ].
Tactic Notation "evalEk'" constr(ZA) constr(AG) tactic(k) :=
L5K.norm_expr; eapply L5KA.zpolyA_val;
[ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity] | cbn [L5KA.zpolyA]; pvz_unfold ZA; reflexivity | solve_modk k ].
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
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
Local Ltac den_tac := first [reflexivity | lia | idtac].
Local Ltac apc_norm :=
repeat match goal with
| |- context [APC.eadd ?a ?b] => let t := eval vm_compute in (APC.eadd a b) in change (APC.eadd a b) with t
| |- context [APC.esub ?a ?b] => let t := eval vm_compute in (APC.esub a b) in change (APC.esub a b) with t
| |- context [APC.escale ?c ?e] => let t := eval vm_compute in (APC.escale c e) in change (APC.escale c e) with t
| |- context [APC.eaddz ?a ?z] => let t := eval vm_compute in (APC.eaddz a z) in change (APC.eaddz a z) with t
end.
Local Ltac zp_norm := repeat (match goal with |- context [(?a <=? ?b) && (?c <? ?d)] => let r := eval vm_compute in ((a <=? b) && (c <? d)) in change ((a <=? b) && (c <? d)) with r end);
repeat (match goal with |- context [2 ^ ?s] => let r := eval vm_compute in (2 ^ s) in change (2 ^ s) with r end); lazy beta iota zeta.
Local Ltac zp_mods := repeat match goal with |- context [(?x mod 18446744073709551616) / _] => rewrite (Z.mod_small x 18446744073709551616) by (zfacts; lia) end.
Local Ltac slotP ZA :=
first [ assumption | reflexivity
| (etransitivity; [eassumption|]; symmetry; eapply word_of_zpoly; [apply (L5K.zagree_all _ _ _ ZA) | cbn [L5KA.zpolyA]; pvz_unfold ZA; zp_norm; f_equal; zp_mods; first [reflexivity | clear; zfacts; lia | zfacts; lia]]) ].
Local Ltac wordP' ZA AG :=
eapply word_of_zpoly; [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity]
| cbn [L5KA.zpolyA]; pvz_unfold ZA; zp_norm; f_equal; zp_mods; first [reflexivity | clear; zfacts; lia | zfacts; lia] ].
Definition KS_ardC : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ardC.regs0 LibSegJa_ardC.regs_out0).
Lemma KS_ardC_ok : BG.kept_ok 60 LibSegJa_ardC.regs0 LibSegJa_ardC.regs_out0 KS_ardC = true. Proof. vm_compute. reflexivity. Qed.
Lemma ardC_conc (HFILL : XIAS0.fill_spec) (HCOPY : XIAS0.copy_spec) (HTLS : XIAS0.tls_spec) fx R M (V : nat -> Z) :
0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 ->
getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 32) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + 48) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + 112) -> getr R (reg 19) = Z_to_bv 64 ((((V 33%nat) + 48) / 8) + 2147450880) -> getr R (reg 20) = Z_to_bv 64 ((((V 33%nat) + 32) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 ((((V 33%nat) + 112) / 8) + 2147450880) ->
140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5.img_clear M 1228800 1261568 ->
L5.u64_at RSEGS M 1289464 2147450880 -> L5.u32_at RSEGS M 1289472 1 -> 6885376 <= ((V 33%nat) - 368) <= 140737488354456 -> aligned ((V 33%nat) - 368) 8 ->
(2147446784 + 17592186048512 <= ((V 33%nat) - 368) \/ ((V 33%nat) - 368) + 864 <= 2147446784) -> (((V 2%nat) - 4096) + 4096 <= ((V 33%nat) - 368) \/ ((V 33%nat) - 368) + 864 <= ((V 2%nat) - 4096)) -> (65536 + 6819840 <= ((V 33%nat) - 368) \/ ((V 33%nat) - 368) + 864 <= 65536) -> L5KA.zeros_at M ((((V 33%nat) - 368) / 8) + 2147450880) 34 ->
L5KA.zeros_at M ((((V 33%nat) + 464) / 8) + 2147450880) 4 -> aligned (V 33%nat) 8 -> L5.writable RSEGS M (V 33%nat) 384 -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 48 ->
L5KA.zeros_at M 2147604812 64 -> L5KA.zeros_at M 2147606604 32 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) ->
L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) ->
L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) 701080 -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) ((V 33%nat) + 464) ->
L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 33%nat) + 24) -> L5.u64_at RSEGS M ((V 2%nat) - 120) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 136) 701632 -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((V 33%nat) + 32) ->
L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 33%nat) + 24) -> L5.u64_at RSEGS M ((V 2%nat) - 160) ((V 33%nat) - 368) -> L5.u64_at RSEGS M ((V 2%nat) - 168) 2147450880 -> L5.u64_at RSEGS M ((V 2%nat) - 176) (V 48%nat) ->
L5.u64_at RSEGS M ((V 2%nat) - 184) 2147450880 ->
exists fx' R' M', mem_grows M M'
/\ (forall a : word, M' a = M a)
/\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
/\ (msteps RSEGS (st fx R 0xabaa8 M) (st fx' R' 0x777d8 M')
/\ (forall x, In x KS_ardC -> getr R' (reg x) = getr R (reg x))
/\ getr R' (reg 1) = Z_to_bv 64 703160
/\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 64)
/\ getr R' (reg 11) = Z_to_bv 64 0
/\ getr R' (reg 12) = Z_to_bv 64 48).
Proof.
intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G8 G9 G18 G19 G20 G21 pvzI10 K1 K2 K3 K4 K5 pvzI11 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36.
pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV43l; move HV43l before pvzI3; pose proof (proj2 pvzI3) as HV43r; move HV43r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV44l; move HV44l before pvzI4; pose proof (proj2 pvzI4) as HV44r; move HV44r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV45l; move HV45l before pvzI5; pose proof (proj2 pvzI5) as HV45r; move HV45r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV46l; move HV46l before pvzI6; pose proof (proj2 pvzI6) as HV46r; move HV46r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV47l; move HV47l before pvzI7; pose proof (proj2 pvzI7) as HV47r; move HV47r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV48l; move HV48l before pvzI8; pose proof (proj2 pvzI8) as HV48r; move HV48r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV49l; move HV49l before pvzI9; pose proof (proj2 pvzI9) as HV49r; move HV49r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K0l; move K0l before pvzI10; pose proof (proj2 pvzI10) as K0r; move K0r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K6l; move K6l before pvzI11; pose proof (proj2 pvzI11) as K6r; move K6r before pvzI11; clear pvzI11.
set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 45%nat => Z_to_bv 64 (V 45%nat) | 46%nat => Z_to_bv 64 (V 46%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | 48%nat => Z_to_bv 64 (V 48%nat) | 49%nat => Z_to_bv 64 (V 49%nat) | _ => getr R (reg j) end) (fun _ => [])).
set (VzN := (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 43%nat => (V 43%nat) | 44%nat => (V 44%nat) | 45%nat => (V 45%nat) | 46%nat => (V 46%nat) | 47%nat => (V 47%nat) | 48%nat => (V 48%nat) | 49%nat => (V 49%nat) | _ => bv_unsigned (getr R (reg j)) end)).
assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
{ unfold VzN. BigLinkZA.za_tac0 50%nat. }
assert (HR: regs_ok E LibSegJa_ardC.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl LibSegJa_ardC.regs0 nth]. apc_norm. repeat split; slotP ZA. }
assert (HK: know_ok RSEGS E M LibSegJa_ardC.kn0).
{ unfold know_ok, LibSegJa_ardC.kn0.
apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | exact (conj K6l K6r)]. }
apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | clear; lia | exact K7]. }
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r; lia | clear - HV33l HV33r K6l K6r; lia | clear - HV33l HV33r K6l K6r; lia | exactA K11]. }
apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r; lia | clear - HV33l HV33r K6l K6r; lia | clear - HV33l HV33r K6l K6r; lia | exactA K12]. }
apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | clear; lia | exact K13]. }
apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r; lia | clear - HV33l HV33r K6l K6r; lia | clear - HV33l HV33r K6l K6r; lia | exactA K14]. }
apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r; lia | clear - HV33l HV33r K6l K6r; lia | clear - HV33l HV33r K6l K6r; lia | exactA K15]. }
apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K16]. }
apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K17]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K18]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K19]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K20]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K21]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K22]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K23]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K24]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K25]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K26]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K27]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K28]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K29]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K30]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K31]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K32]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K33]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K34]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K35]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K36]. }
apply Forall_nil. }
pvz_hg ltac:(idtac; destruct (LibSegJa_ardC.seg_sound_ax HFILL HCOPY HTLS fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
change LibSegJa_ardC.NX0 with 60%nat in Hag.
exists fx', R', M'. pvz_linconj. split. exact Hgr.
assert (FRW: forall a : word, M' a = M a).
{ intros a. apply Hfr. unfold LibSegJa_ardC.F0.
apply L5K.outside_nil_e. }
split. exact FRW.
split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
apply L5K.nth_error_single in Hnth. subst ps.
change (SR.ps_pc LibSegJa_ardC.ps0) with 0x777d8 in Hms. change (SR.ps_regs LibSegJa_ardC.ps0) with (map (fun i => (i, nth i LibSegJa_ardC.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
change (SR.ps_cells LibSegJa_ardC.ps0) with LibSegJa_ardC.cells0 in Hcells.
split. { exact Hms. }
split. { intros j Hj. apply (BG.kept_regs E E' R R' LibSegJa_ardC.regs0 LibSegJa_ardC.regs_out0 60 KS_ardC KS_ardC_ok HR Hag Hregs j Hj). }
split. { rewrite (BG.out_reg LibSegJa_ardC.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth LibSegJa_ardC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { rewrite (BG.out_reg LibSegJa_ardC.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth LibSegJa_ardC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { rewrite (BG.out_reg LibSegJa_ardC.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth LibSegJa_ardC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
rewrite (BG.out_reg LibSegJa_ardC.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth LibSegJa_ardC.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.
Definition KS_ardD : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ardD.regs0 LibSegJa_ardD.regs_out0).
Lemma KS_ardD_ok : BG.kept_ok 60 LibSegJa_ardD.regs0 LibSegJa_ardD.regs_out0 KS_ardD = true. Proof. vm_compute. reflexivity. Qed.
Lemma ardD_conc (HFILL : XIAS0.fill_spec) (HCOPY : XIAS0.copy_spec) (HTLS : XIAS0.tls_spec) fx R M (V : nat -> Z) :
0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 ->
getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 32) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + 48) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + 112) -> getr R (reg 19) = Z_to_bv 64 ((((V 33%nat) + 48) / 8) + 2147450880) -> getr R (reg 20) = Z_to_bv 64 ((((V 33%nat) + 32) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 ((((V 33%nat) + 112) / 8) + 2147450880) ->
140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5.img_clear M 1228800 1261568 ->
L5.u64_at RSEGS M 1289464 2147450880 -> L5.u32_at RSEGS M 1289472 1 -> 6885376 <= ((V 33%nat) - 368) <= 140737488354456 -> aligned ((V 33%nat) - 368) 8 ->
(2147446784 + 17592186048512 <= ((V 33%nat) - 368) \/ ((V 33%nat) - 368) + 864 <= 2147446784) -> (((V 2%nat) - 4096) + 4096 <= ((V 33%nat) - 368) \/ ((V 33%nat) - 368) + 864 <= ((V 2%nat) - 4096)) -> (65536 + 6819840 <= ((V 33%nat) - 368) \/ ((V 33%nat) - 368) + 864 <= 65536) -> L5KA.zeros_at M ((((V 33%nat) - 368) / 8) + 2147450880) 34 ->
L5KA.zeros_at M ((((V 33%nat) + 464) / 8) + 2147450880) 4 -> aligned (V 33%nat) 8 -> L5.writable RSEGS M (V 33%nat) 384 -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 48 ->
L5KA.zeros_at M 2147604812 64 -> L5KA.zeros_at M 2147606604 32 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) ->
L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) ->
L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) 701080 -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) ((V 33%nat) + 464) ->
L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 33%nat) + 24) -> L5.u64_at RSEGS M ((V 2%nat) - 120) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 136) 701632 -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((V 33%nat) + 32) ->
L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 33%nat) + 24) -> L5.u64_at RSEGS M ((V 2%nat) - 160) ((V 33%nat) - 368) -> L5.u64_at RSEGS M ((V 2%nat) - 168) 2147450880 -> L5.u64_at RSEGS M ((V 2%nat) - 176) (V 48%nat) ->
L5.u64_at RSEGS M ((V 2%nat) - 184) 2147450880 -> L5.u64_at RSEGS M ((V 33%nat) - 368) 1245864 -> L5.u64_at RSEGS M ((V 33%nat) - 208) ((V 33%nat) - 352) ->
exists fx' R' M', mem_grows M M'
/\ (forall a : word, ~ (((V 33%nat) + 48) <= bv_unsigned a < ((V 33%nat) + 48) + 8) -> ~ (((V 33%nat) + 264) <= bv_unsigned a < ((V 33%nat) + 264) + 16) -> M' a = M a)
/\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 48) <= i < ((V 33%nat) + 48) + 8) -> ~ (((V 33%nat) + 264) <= i < ((V 33%nat) + 264) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
/\ (msteps RSEGS (st fx R 0xabab8 M) (st fx' R' 0x777d8 M')
/\ (forall x, In x KS_ardD -> getr R' (reg x) = getr R (reg x))
/\ getr R' (reg 1) = Z_to_bv 64 701772
/\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
/\ getr R' (reg 9) = Z_to_bv 64 ((V 33%nat) + 24)
/\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 280)
/\ getr R' (reg 11) = Z_to_bv 64 0
/\ getr R' (reg 12) = Z_to_bv 64 16
/\ getr R' (reg 18) = Z_to_bv 64 ((V 33%nat) + 296)
/\ getr R' (reg 19) = Z_to_bv 64 2147450880
/\ getr R' (reg 20) = Z_to_bv 64 (V 48%nat)
/\ getr R' (reg 21) = Z_to_bv 64 2147450880
/\ L5.u64_at RSEGS M' ((V 33%nat) + 272) ((V 33%nat) - 352)
/\ L5.u64_at RSEGS M' ((V 33%nat) + 264) ((V 33%nat) - 368)
/\ L5.u64_at RSEGS M' ((V 33%nat) + 48) 1231968).
Proof.
intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G8 G9 G18 G19 G20 G21 pvzI10 K1 K2 K3 K4 K5 pvzI11 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38.
pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV43l; move HV43l before pvzI3; pose proof (proj2 pvzI3) as HV43r; move HV43r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV44l; move HV44l before pvzI4; pose proof (proj2 pvzI4) as HV44r; move HV44r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV45l; move HV45l before pvzI5; pose proof (proj2 pvzI5) as HV45r; move HV45r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV46l; move HV46l before pvzI6; pose proof (proj2 pvzI6) as HV46r; move HV46r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV47l; move HV47l before pvzI7; pose proof (proj2 pvzI7) as HV47r; move HV47r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV48l; move HV48l before pvzI8; pose proof (proj2 pvzI8) as HV48r; move HV48r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV49l; move HV49l before pvzI9; pose proof (proj2 pvzI9) as HV49r; move HV49r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K0l; move K0l before pvzI10; pose proof (proj2 pvzI10) as K0r; move K0r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K6l; move K6l before pvzI11; pose proof (proj2 pvzI11) as K6r; move K6r before pvzI11; clear pvzI11.
set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 45%nat => Z_to_bv 64 (V 45%nat) | 46%nat => Z_to_bv 64 (V 46%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | 48%nat => Z_to_bv 64 (V 48%nat) | 49%nat => Z_to_bv 64 (V 49%nat) | _ => getr R (reg j) end) (fun _ => [])).
set (VzN := (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 43%nat => (V 43%nat) | 44%nat => (V 44%nat) | 45%nat => (V 45%nat) | 46%nat => (V 46%nat) | 47%nat => (V 47%nat) | 48%nat => (V 48%nat) | 49%nat => (V 49%nat) | _ => bv_unsigned (getr R (reg j)) end)).
assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
{ unfold VzN. BigLinkZA.za_tac0 50%nat. }
assert (HR: regs_ok E LibSegJa_ardD.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl LibSegJa_ardD.regs0 nth]. apc_norm. repeat split; slotP ZA. }
assert (HK: know_ok RSEGS E M LibSegJa_ardD.kn0).
{ unfold know_ok, LibSegJa_ardD.kn0.
apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | exact (conj K6l K6r)]. }
apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | clear; lia | exact K7]. }
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r; lia | clear - HV33l HV33r K6l K6r; lia | clear - HV33l HV33r K6l K6r; lia | exactA K11]. }
apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r; lia | clear - HV33l HV33r K6l K6r; lia | clear - HV33l HV33r K6l K6r; lia | exactA K12]. }
apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | clear; lia | exact K13]. }
apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r; lia | clear - HV33l HV33r K6l K6r; lia | clear - HV33l HV33r K6l K6r; lia | exactA K14]. }
apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r; lia | clear - HV33l HV33r K6l K6r; lia | clear - HV33l HV33r K6l K6r; lia | exactA K15]. }
apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K16]. }
apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K17]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K18]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K19]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K20]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K21]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K22]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K23]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K24]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K25]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K26]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K27]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K28]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K29]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K30]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K31]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K32]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K33]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K34]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K35]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K36]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r; lia | clear - HV33l HV33r K6l K6r; lia | exactA K37]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | clear - HV33l HV33r K6l K6r; lia | clear - HV33l HV33r K6l K6r; lia | exactA K38]. }
apply Forall_nil. }
pvz_hg ltac:(idtac; destruct (LibSegJa_ardD.seg_sound_ax HFILL HCOPY HTLS fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
change LibSegJa_ardD.NX0 with 60%nat in Hag.
exists fx', R', M'. pvz_linconj. split. exact Hgr.
assert (FRW: forall a : word, ~ (((V 33%nat) + 48) <= bv_unsigned a < ((V 33%nat) + 48) + 8) -> ~ (((V 33%nat) + 264) <= bv_unsigned a < ((V 33%nat) + 264) + 16) -> M' a = M a).
{ intros a Hn0 Hn1. apply Hfr. unfold LibSegJa_ardD.F0.
eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r Hn0; lia |].
eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r Hn1; lia |].
apply L5K.outside_nil_e. }
split. exact FRW.
split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
apply L5K.nth_error_single in Hnth. subst ps.
change (SR.ps_pc LibSegJa_ardD.ps0) with 0x777d8 in Hms. change (SR.ps_regs LibSegJa_ardD.ps0) with (map (fun i => (i, nth i LibSegJa_ardD.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
change (SR.ps_cells LibSegJa_ardD.ps0) with LibSegJa_ardD.cells0 in Hcells.
split. { exact Hms. }
split. { intros j Hj. apply (BG.kept_regs E E' R R' LibSegJa_ardD.regs0 LibSegJa_ardD.regs_out0 60 KS_ardD KS_ardD_ok HR Hag Hregs j Hj). }
split. { rewrite (BG.out_reg LibSegJa_ardD.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth LibSegJa_ardD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { rewrite (BG.out_reg LibSegJa_ardD.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth LibSegJa_ardD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { rewrite (BG.out_reg LibSegJa_ardD.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth LibSegJa_ardD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { rewrite (BG.out_reg LibSegJa_ardD.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth LibSegJa_ardD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { rewrite (BG.out_reg LibSegJa_ardD.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth LibSegJa_ardD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { rewrite (BG.out_reg LibSegJa_ardD.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth LibSegJa_ardD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { rewrite (BG.out_reg LibSegJa_ardD.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth LibSegJa_ardD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { rewrite (BG.out_reg LibSegJa_ardD.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth LibSegJa_ardD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { rewrite (BG.out_reg LibSegJa_ardD.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth LibSegJa_ardD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { rewrite (BG.out_reg LibSegJa_ardD.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth LibSegJa_ardD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r) | clear; lia]. }
split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r) | clear; lia]. }
eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.
Definition KS_ardE : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ardE.regs0 LibSegJa_ardE.regs_out0).
Lemma KS_ardE_ok : BG.kept_ok 60 LibSegJa_ardE.regs0 LibSegJa_ardE.regs_out0 KS_ardE = true. Proof. vm_compute. reflexivity. Qed.
Lemma ardE_conc (HFILL : XIAS0.fill_spec) (HCOPY : XIAS0.copy_spec) (HTLS : XIAS0.tls_spec) fx R M (V : nat -> Z) :
0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 ->
getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 32) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + 24) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + 296) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5.img_clear M 1228800 1261568 ->
L5.u64_at RSEGS M 1289464 2147450880 -> L5.u32_at RSEGS M 1289472 1 -> 6885376 <= ((V 33%nat) - 368) <= 140737488354456 -> aligned ((V 33%nat) - 368) 8 ->
(2147446784 + 17592186048512 <= ((V 33%nat) - 368) \/ ((V 33%nat) - 368) + 864 <= 2147446784) -> (((V 2%nat) - 4096) + 4096 <= ((V 33%nat) - 368) \/ ((V 33%nat) - 368) + 864 <= ((V 2%nat) - 4096)) -> (65536 + 6819840 <= ((V 33%nat) - 368) \/ ((V 33%nat) - 368) + 864 <= 65536) -> L5KA.zeros_at M ((((V 33%nat) - 368) / 8) + 2147450880) 34 ->
L5KA.zeros_at M ((((V 33%nat) + 464) / 8) + 2147450880) 4 -> aligned (V 33%nat) 8 -> L5.writable RSEGS M (V 33%nat) 384 -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 48 ->
L5KA.zeros_at M 2147604812 64 -> L5KA.zeros_at M 2147606604 32 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) ->
L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) ->
L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) 701080 -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) ((V 33%nat) + 464) ->
L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 33%nat) + 24) -> L5.u64_at RSEGS M ((V 2%nat) - 120) (V 47%nat) ->
exists fx' R' M', mem_grows M M'
/\ (forall a : word, ~ (((V 33%nat) + 296) <= bv_unsigned a < ((V 33%nat) + 296) + 8) -> M' a = M a)
/\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 296) <= i < ((V 33%nat) + 296) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
/\ (msteps RSEGS (st fx R 0xab54c M) (st fx' R' 0x777d8 M')
/\ (forall x, In x KS_ardE -> getr R' (reg x) = getr R (reg x))
/\ getr R' (reg 1) = Z_to_bv 64 701816
/\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 304)
/\ getr R' (reg 11) = Z_to_bv 64 0
/\ getr R' (reg 12) = Z_to_bv 64 16
/\ getr R' (reg 18) = Z_to_bv 64 ((V 33%nat) + 304)
/\ L5.u64_at RSEGS M' ((V 33%nat) + 296) 16384).
Proof.
intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G8 G9 G18 G19 G21 pvzI10 K1 K2 K3 K4 K5 pvzI11 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29.
pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV43l; move HV43l before pvzI3; pose proof (proj2 pvzI3) as HV43r; move HV43r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV44l; move HV44l before pvzI4; pose proof (proj2 pvzI4) as HV44r; move HV44r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV45l; move HV45l before pvzI5; pose proof (proj2 pvzI5) as HV45r; move HV45r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV46l; move HV46l before pvzI6; pose proof (proj2 pvzI6) as HV46r; move HV46r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV47l; move HV47l before pvzI7; pose proof (proj2 pvzI7) as HV47r; move HV47r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV48l; move HV48l before pvzI8; pose proof (proj2 pvzI8) as HV48r; move HV48r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV49l; move HV49l before pvzI9; pose proof (proj2 pvzI9) as HV49r; move HV49r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K0l; move K0l before pvzI10; pose proof (proj2 pvzI10) as K0r; move K0r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K6l; move K6l before pvzI11; pose proof (proj2 pvzI11) as K6r; move K6r before pvzI11; clear pvzI11.
set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 45%nat => Z_to_bv 64 (V 45%nat) | 46%nat => Z_to_bv 64 (V 46%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | 48%nat => Z_to_bv 64 (V 48%nat) | 49%nat => Z_to_bv 64 (V 49%nat) | _ => getr R (reg j) end) (fun _ => [])).
set (VzN := (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 43%nat => (V 43%nat) | 44%nat => (V 44%nat) | 45%nat => (V 45%nat) | 46%nat => (V 46%nat) | 47%nat => (V 47%nat) | 48%nat => (V 48%nat) | 49%nat => (V 49%nat) | _ => bv_unsigned (getr R (reg j)) end)).
assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
{ unfold VzN. BigLinkZA.za_tac0 50%nat. }
assert (HR: regs_ok E LibSegJa_ardE.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl LibSegJa_ardE.regs0 nth]. apc_norm. repeat split; slotP ZA. }
assert (HK: know_ok RSEGS E M LibSegJa_ardE.kn0).
{ unfold know_ok, LibSegJa_ardE.kn0.
apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | exact (conj K6l K6r)]. }
apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | clear; lia | exact K7]. }
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r; lia | clear - HV33l HV33r K6l K6r; lia | clear - HV33l HV33r K6l K6r; lia | exactA K11]. }
apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r; lia | clear - HV33l HV33r K6l K6r; lia | clear - HV33l HV33r K6l K6r; lia | exactA K12]. }
apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | clear; lia | exact K13]. }
apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r; lia | clear - HV33l HV33r K6l K6r; lia | clear - HV33l HV33r K6l K6r; lia | exactA K14]. }
apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r; lia | clear - HV33l HV33r K6l K6r; lia | clear - HV33l HV33r K6l K6r; lia | exactA K15]. }
apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K16]. }
apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K17]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K18]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K19]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K20]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K21]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K22]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K23]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K24]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K25]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K26]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K27]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K28]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K29]. }
apply Forall_nil. }
pvz_hg ltac:(idtac; destruct (LibSegJa_ardE.seg_sound_ax HFILL HCOPY HTLS fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
change LibSegJa_ardE.NX0 with 60%nat in Hag.
exists fx', R', M'. pvz_linconj. split. exact Hgr.
assert (FRW: forall a : word, ~ (((V 33%nat) + 296) <= bv_unsigned a < ((V 33%nat) + 296) + 8) -> M' a = M a).
{ intros a Hn0. apply Hfr. unfold LibSegJa_ardE.F0.
eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r Hn0; lia |].
apply L5K.outside_nil_e. }
split. exact FRW.
split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
apply L5K.nth_error_single in Hnth. subst ps.
change (SR.ps_pc LibSegJa_ardE.ps0) with 0x777d8 in Hms. change (SR.ps_regs LibSegJa_ardE.ps0) with (map (fun i => (i, nth i LibSegJa_ardE.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
change (SR.ps_cells LibSegJa_ardE.ps0) with LibSegJa_ardE.cells0 in Hcells.
split. { exact Hms. }
split. { intros j Hj. apply (BG.kept_regs E E' R R' LibSegJa_ardE.regs0 LibSegJa_ardE.regs_out0 60 KS_ardE KS_ardE_ok HR Hag Hregs j Hj). }
split. { rewrite (BG.out_reg LibSegJa_ardE.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth LibSegJa_ardE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { rewrite (BG.out_reg LibSegJa_ardE.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth LibSegJa_ardE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { rewrite (BG.out_reg LibSegJa_ardE.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth LibSegJa_ardE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { rewrite (BG.out_reg LibSegJa_ardE.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth LibSegJa_ardE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { rewrite (BG.out_reg LibSegJa_ardE.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth LibSegJa_ardE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.
Definition KS_ardF : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ardF.regs0 LibSegJa_ardF.regs_out0).
Lemma KS_ardF_ok : BG.kept_ok 60 LibSegJa_ardF.regs0 LibSegJa_ardF.regs_out0 KS_ardF = true. Proof. vm_compute. reflexivity. Qed.
Lemma ardF_conc (HFILL : XIAS0.fill_spec) (HCOPY : XIAS0.copy_spec) (HTLS : XIAS0.tls_spec) fx R M (V : nat -> Z) :
0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 ->
getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 32) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + 24) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + 304) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
exists fx' R' M', mem_grows M M'
/\ (forall a : word, M' a = M a)
/\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
/\ (msteps RSEGS (st fx R 0xab578 M) (st fx' R' 0x12b3e4 M')
/\ (forall x, In x KS_ardF -> getr R' (reg x) = getr R (reg x))
/\ getr R' (reg 1) = Z_to_bv 64 701824
/\ getr R' (reg 10) = Z_to_bv 64 16384).
Proof.
intros pvzI1 pvzI2 G2 G8 G9 G18 G19 G21.
pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2.
set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | _ => getr R (reg j) end) (fun _ => [])).
set (VzN := (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | _ => bv_unsigned (getr R (reg j)) end)).
assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
{ unfold VzN. BigLinkZA.za_tac0 34%nat. }
assert (HR: regs_ok E LibSegJa_ardF.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl LibSegJa_ardF.regs0 nth]. apc_norm. repeat split; slotP ZA. }
assert (HK: know_ok RSEGS E M LibSegJa_ardF.kn0).
{ unfold know_ok, LibSegJa_ardF.kn0.
apply Forall_nil. }
pvz_hg ltac:(idtac; destruct (LibSegJa_ardF.seg_sound_ax HFILL HCOPY HTLS fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
change LibSegJa_ardF.NX0 with 60%nat in Hag.
exists fx', R', M'. pvz_linconj. split. exact Hgr.
assert (FRW: forall a : word, M' a = M a).
{ intros a. apply Hfr. unfold LibSegJa_ardF.F0.
apply L5K.outside_nil_e. }
split. exact FRW.
split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
apply L5K.nth_error_single in Hnth. subst ps.
change (SR.ps_pc LibSegJa_ardF.ps0) with 0x12b3e4 in Hms. change (SR.ps_regs LibSegJa_ardF.ps0) with (map (fun i => (i, nth i LibSegJa_ardF.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
change (SR.ps_cells LibSegJa_ardF.ps0) with LibSegJa_ardF.cells0 in Hcells.
split. { exact Hms. }
split. { intros j Hj. apply (BG.kept_regs E E' R R' LibSegJa_ardF.regs0 LibSegJa_ardF.regs_out0 60 KS_ardF KS_ardF_ok HR Hag Hregs j Hj). }
split. { rewrite (BG.out_reg LibSegJa_ardF.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth LibSegJa_ardF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
rewrite (BG.out_reg LibSegJa_ardF.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth LibSegJa_ardF.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.
Definition KS_ardG : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ardG.regs0 LibSegJa_ardG.regs_out0).
Lemma KS_ardG_ok : BG.kept_ok 60 LibSegJa_ardG.regs0 LibSegJa_ardG.regs_out0 KS_ardG = true. Proof. vm_compute. reflexivity. Qed.
Lemma ardG_conc (HFILL : XIAS0.fill_spec) (HCOPY : XIAS0.copy_spec) (HTLS : XIAS0.tls_spec) fx R M (V : nat -> Z) :
0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 ->
getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 32) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + 24) -> getr R (reg 10) = Z_to_bv 64 (V 35%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + 304) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5.img_clear M 1228800 1261568 ->
L5.u64_at RSEGS M 1289464 2147450880 -> L5.u32_at RSEGS M 1289472 1 -> 6885376 <= ((V 33%nat) - 368) <= 140737488354456 -> aligned ((V 33%nat) - 368) 8 ->
(2147446784 + 17592186048512 <= ((V 33%nat) - 368) \/ ((V 33%nat) - 368) + 864 <= 2147446784) -> (((V 2%nat) - 4096) + 4096 <= ((V 33%nat) - 368) \/ ((V 33%nat) - 368) + 864 <= ((V 2%nat) - 4096)) -> (65536 + 6819840 <= ((V 33%nat) - 368) \/ ((V 33%nat) - 368) + 864 <= 65536) -> L5KA.zeros_at M ((((V 33%nat) - 368) / 8) + 2147450880) 34 ->
L5KA.zeros_at M ((((V 33%nat) + 464) / 8) + 2147450880) 4 -> aligned (V 33%nat) 8 -> L5.writable RSEGS M (V 33%nat) 384 -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 48 ->
L5KA.zeros_at M 2147604812 64 -> L5KA.zeros_at M 2147606604 32 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) ->
L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) ->
L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) 701080 -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) ((V 33%nat) + 464) ->
L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 33%nat) + 24) -> L5.u64_at RSEGS M ((V 2%nat) - 120) (V 47%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 464) 1231512 -> L5.u64_at RSEGS M ((V 33%nat) + 472) 16777216 ->
L5.u32_at RSEGS M ((V 33%nat) + 488) 1024 ->
exists fx' R' M', mem_grows M M'
/\ (forall a : word, ~ (((V 33%nat) + 288) <= bv_unsigned a < ((V 33%nat) + 288) + 8) -> ~ (((V 33%nat) + 304) <= bv_unsigned a < ((V 33%nat) + 304) + 8) -> ~ (((V 33%nat) + 320) <= bv_unsigned a < ((V 33%nat) + 320) + 4) -> ~ (((V 33%nat) + 328) <= bv_unsigned a < ((V 33%nat) + 328) + 8) -> M' a = M a)
/\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 288) <= i < ((V 33%nat) + 288) + 8) -> ~ (((V 33%nat) + 304) <= i < ((V 33%nat) + 304) + 8) -> ~ (((V 33%nat) + 320) <= i < ((V 33%nat) + 320) + 4) -> ~ (((V 33%nat) + 328) <= i < ((V 33%nat) + 328) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
/\ (msteps RSEGS (st fx R 0xab580 M) (st fx' R' 0x777d8 M')
/\ (forall x, In x KS_ardG -> getr R' (reg x) = getr R (reg x))
/\ getr R' (reg 1) = Z_to_bv 64 701248
/\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 80)
/\ getr R' (reg 8) = Z_to_bv 64 (V 33%nat)
/\ getr R' (reg 9) = Z_to_bv 64 ((V 33%nat) + 336)
/\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 336)
/\ getr R' (reg 11) = Z_to_bv 64 0
/\ getr R' (reg 12) = Z_to_bv 64 48
/\ getr R' (reg 18) = Z_to_bv 64 ((V 33%nat) + 24)
/\ getr R' (reg 19) = Z_to_bv 64 (V 47%nat)
/\ getr R' (reg 20) = Z_to_bv 64 ((V 33%nat) + 360)
/\ L5.u64_at RSEGS M' ((V 33%nat) + 328) 16777216
/\ L5.u32_at RSEGS M' ((V 33%nat) + 320) 1024
/\ L5.u64_at RSEGS M' ((V 33%nat) + 304) (V 35%nat)
/\ L5.u64_at RSEGS M' ((V 33%nat) + 288) (V 35%nat)).
Proof.
intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 G2 G8 G9 G10 G18 G19 G21 pvzI11 K1 K2 K3 K4 K5 pvzI12 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32.
pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV43l; move HV43l before pvzI4; pose proof (proj2 pvzI4) as HV43r; move HV43r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV44l; move HV44l before pvzI5; pose proof (proj2 pvzI5) as HV44r; move HV44r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV45l; move HV45l before pvzI6; pose proof (proj2 pvzI6) as HV45r; move HV45r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV46l; move HV46l before pvzI7; pose proof (proj2 pvzI7) as HV46r; move HV46r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV47l; move HV47l before pvzI8; pose proof (proj2 pvzI8) as HV47r; move HV47r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV48l; move HV48l before pvzI9; pose proof (proj2 pvzI9) as HV48r; move HV48r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV49l; move HV49l before pvzI10; pose proof (proj2 pvzI10) as HV49r; move HV49r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K0l; move K0l before pvzI11; pose proof (proj2 pvzI11) as K0r; move K0r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K6l; move K6l before pvzI12; pose proof (proj2 pvzI12) as K6r; move K6r before pvzI12; clear pvzI12.
set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 45%nat => Z_to_bv 64 (V 45%nat) | 46%nat => Z_to_bv 64 (V 46%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | 48%nat => Z_to_bv 64 (V 48%nat) | 49%nat => Z_to_bv 64 (V 49%nat) | _ => getr R (reg j) end) (fun _ => [])).
set (VzN := (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 35%nat => (V 35%nat) | 43%nat => (V 43%nat) | 44%nat => (V 44%nat) | 45%nat => (V 45%nat) | 46%nat => (V 46%nat) | 47%nat => (V 47%nat) | 48%nat => (V 48%nat) | 49%nat => (V 49%nat) | _ => bv_unsigned (getr R (reg j)) end)).
assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
{ unfold VzN. BigLinkZA.za_tac0 50%nat. }
assert (HR: regs_ok E LibSegJa_ardG.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl LibSegJa_ardG.regs0 nth]. apc_norm. repeat split; slotP ZA. }
assert (HK: know_ok RSEGS E M LibSegJa_ardG.kn0).
{ unfold know_ok, LibSegJa_ardG.kn0.
apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | exact (conj K6l K6r)]. }
apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | clear; lia | exact K7]. }
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r; lia | clear - HV33l HV33r K6l K6r; lia | clear - HV33l HV33r K6l K6r; lia | exactA K11]. }
apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r; lia | clear - HV33l HV33r K6l K6r; lia | clear - HV33l HV33r K6l K6r; lia | exactA K12]. }
apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | clear; lia | exact K13]. }
apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r; lia | clear - HV33l HV33r K6l K6r; lia | clear - HV33l HV33r K6l K6r; lia | exactA K14]. }
apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r; lia | clear - HV33l HV33r K6l K6r; lia | clear - HV33l HV33r K6l K6r; lia | exactA K15]. }
apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K16]. }
apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K17]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K18]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K19]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K20]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K21]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K22]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K23]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K24]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K25]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K26]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K27]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K28]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K29]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r; lia | clear - HV33l HV33r K6l K6r; lia | exactA K30]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r; lia | clear - HV33l HV33r K6l K6r; lia | exactA K31]. }
apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r; lia | clear - HV33l HV33r K6l K6r; lia | exactA K32]. }
apply Forall_nil. }
pvz_hg ltac:(idtac; destruct (LibSegJa_ardG.seg_sound_ax HFILL HCOPY HTLS fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
change LibSegJa_ardG.NX0 with 60%nat in Hag.
exists fx', R', M'. pvz_linconj. split. exact Hgr.
assert (FRW: forall a : word, ~ (((V 33%nat) + 288) <= bv_unsigned a < ((V 33%nat) + 288) + 8) -> ~ (((V 33%nat) + 304) <= bv_unsigned a < ((V 33%nat) + 304) + 8) -> ~ (((V 33%nat) + 320) <= bv_unsigned a < ((V 33%nat) + 320) + 4) -> ~ (((V 33%nat) + 328) <= bv_unsigned a < ((V 33%nat) + 328) + 8) -> M' a = M a).
{ intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold LibSegJa_ardG.F0.
eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r Hn0; lia |].
eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r Hn1; lia |].
eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r Hn2; lia |].
eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r Hn3; lia |].
apply L5K.outside_nil_e. }
split. exact FRW.
split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
apply L5K.nth_error_single in Hnth. subst ps.
change (SR.ps_pc LibSegJa_ardG.ps0) with 0x777d8 in Hms. change (SR.ps_regs LibSegJa_ardG.ps0) with (map (fun i => (i, nth i LibSegJa_ardG.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
change (SR.ps_cells LibSegJa_ardG.ps0) with LibSegJa_ardG.cells0 in Hcells.
split. { exact Hms. }
split. { intros j Hj. apply (BG.kept_regs E E' R R' LibSegJa_ardG.regs0 LibSegJa_ardG.regs_out0 60 KS_ardG KS_ardG_ok HR Hag Hregs j Hj). }
split. { rewrite (BG.out_reg LibSegJa_ardG.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth LibSegJa_ardG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { rewrite (BG.out_reg LibSegJa_ardG.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth LibSegJa_ardG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { rewrite (BG.out_reg LibSegJa_ardG.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth LibSegJa_ardG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { rewrite (BG.out_reg LibSegJa_ardG.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth LibSegJa_ardG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { rewrite (BG.out_reg LibSegJa_ardG.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth LibSegJa_ardG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { rewrite (BG.out_reg LibSegJa_ardG.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth LibSegJa_ardG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { rewrite (BG.out_reg LibSegJa_ardG.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth LibSegJa_ardG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { rewrite (BG.out_reg LibSegJa_ardG.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth LibSegJa_ardG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { rewrite (BG.out_reg LibSegJa_ardG.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth LibSegJa_ardG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { rewrite (BG.out_reg LibSegJa_ardG.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth LibSegJa_ardG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r) | evalEk' ZA Hag ltac:(clear - HV35l HV35r) | clear; lia]. }
eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r) | evalEk' ZA Hag ltac:(clear - HV35l HV35r) | clear; lia].
Qed.
Definition KS_ardH : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ardH.regs0 LibSegJa_ardH.regs_out0).
Lemma KS_ardH_ok : BG.kept_ok 60 LibSegJa_ardH.regs0 LibSegJa_ardH.regs_out0 KS_ardH = true. Proof. vm_compute. reflexivity. Qed.
Lemma ardH_conc (HFILL : XIAS0.fill_spec) (HCOPY : XIAS0.copy_spec) (HTLS : XIAS0.tls_spec) fx R M (V : nat -> Z) :
0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 ->
getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + 336) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + 24) -> getr R (reg 20) = Z_to_bv 64 ((V 33%nat) + 360) -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 ->
exists fx' R' M', mem_grows M M'
/\ (forall a : word, ~ (((V 2%nat) - 68) <= bv_unsigned a < ((V 2%nat) - 68) + 8) -> M' a = M a)
/\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 68) <= i < ((V 2%nat) - 68) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
/\ (msteps RSEGS (st fx R 0xab340 M) (st fx' R' 0xab610 M')
/\ (forall x, In x KS_ardH -> getr R' (reg x) = getr R (reg x))
/\ getr R' (reg 1) = Z_to_bv 64 701272
/\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 360)
/\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 64)
/\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 68)
/\ L5.u32_at RSEGS M' ((V 2%nat) - 68) 0
/\ L5.u32_at RSEGS M' ((V 2%nat) - 64) 0).
Proof.
intros pvzI1 pvzI2 G2 G8 G9 G18 G20 G21 pvzI3 K1 K2.
pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as K0l; move K0l before pvzI3; pose proof (proj2 pvzI3) as K0r; move K0r before pvzI3; clear pvzI3.
set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | _ => getr R (reg j) end) (fun _ => [])).
set (VzN := (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | _ => bv_unsigned (getr R (reg j)) end)).
assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
{ unfold VzN. BigLinkZA.za_tac0 34%nat. }
assert (HR: regs_ok E LibSegJa_ardH.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl LibSegJa_ardH.regs0 nth]. apc_norm. repeat split; slotP ZA. }
assert (HK: know_ok RSEGS E M LibSegJa_ardH.kn0).
{ unfold know_ok, LibSegJa_ardH.kn0.
apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
apply Forall_nil. }
pvz_hg ltac:(idtac; destruct (LibSegJa_ardH.seg_sound_ax HFILL HCOPY HTLS fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
change LibSegJa_ardH.NX0 with 60%nat in Hag.
exists fx', R', M'. pvz_linconj. split. exact Hgr.
assert (FRW: forall a : word, ~ (((V 2%nat) - 68) <= bv_unsigned a < ((V 2%nat) - 68) + 8) -> M' a = M a).
{ intros a Hn0. apply Hfr. unfold LibSegJa_ardH.F0.
eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
apply L5K.outside_nil_e. }
split. exact FRW.
split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
apply L5K.nth_error_single in Hnth. subst ps.
change (SR.ps_pc LibSegJa_ardH.ps0) with 0xab610 in Hms. change (SR.ps_regs LibSegJa_ardH.ps0) with (map (fun i => (i, nth i LibSegJa_ardH.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
change (SR.ps_cells LibSegJa_ardH.ps0) with LibSegJa_ardH.cells0 in Hcells.
split. { exact Hms. }
split. { intros j Hj. apply (BG.kept_regs E E' R R' LibSegJa_ardH.regs0 LibSegJa_ardH.regs_out0 60 KS_ardH KS_ardH_ok HR Hag Hregs j Hj). }
split. { rewrite (BG.out_reg LibSegJa_ardH.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth LibSegJa_ardH.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { rewrite (BG.out_reg LibSegJa_ardH.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth LibSegJa_ardH.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { rewrite (BG.out_reg LibSegJa_ardH.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth LibSegJa_ardH.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { rewrite (BG.out_reg LibSegJa_ardH.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth LibSegJa_ardH.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.
Definition KS_ardZ : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_ardZ.regs0 LibSegJa_ardZ.regs_out0).
Lemma KS_ardZ_ok : BG.kept_ok 60 LibSegJa_ardZ.regs0 LibSegJa_ardZ.regs_out0 KS_ardZ = true. Proof. vm_compute. reflexivity. Qed.
Lemma ardZ_conc (HFILL : XIAS0.fill_spec) (HCOPY : XIAS0.copy_spec) (HTLS : XIAS0.tls_spec) fx R M (V : nat -> Z) :
0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 ->
getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) ->
140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) ->
L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) ->
L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) ->
exists fx' R' M', mem_grows M M'
/\ (forall a : word, M' a = M a)
/\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
/\ (msteps RSEGS (st fx R 0xab358 M) (st fx' R' 0xab378 M')
/\ (forall x, In x KS_ardZ -> getr R' (reg x) = getr R (reg x))
/\ getr R' (reg 1) = Z_to_bv 64 (V 43%nat)
/\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
/\ getr R' (reg 8) = Z_to_bv 64 (V 44%nat)
/\ getr R' (reg 9) = Z_to_bv 64 (V 45%nat)
/\ getr R' (reg 18) = Z_to_bv 64 (V 46%nat)
/\ getr R' (reg 19) = Z_to_bv 64 (V 47%nat)
/\ getr R' (reg 20) = Z_to_bv 64 (V 48%nat)
/\ getr R' (reg 21) = Z_to_bv 64 (V 49%nat)).
Proof.
intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 pvzI9 K1 K2 K3 K4 K5 K6 K7 K8 K9.
pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV43l; move HV43l before pvzI2; pose proof (proj2 pvzI2) as HV43r; move HV43r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV44l; move HV44l before pvzI3; pose proof (proj2 pvzI3) as HV44r; move HV44r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV45l; move HV45l before pvzI4; pose proof (proj2 pvzI4) as HV45r; move HV45r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV46l; move HV46l before pvzI5; pose proof (proj2 pvzI5) as HV46r; move HV46r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV47l; move HV47l before pvzI6; pose proof (proj2 pvzI6) as HV47r; move HV47r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV48l; move HV48l before pvzI7; pose proof (proj2 pvzI7) as HV48r; move HV48r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV49l; move HV49l before pvzI8; pose proof (proj2 pvzI8) as HV49r; move HV49r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K0l; move K0l before pvzI9; pose proof (proj2 pvzI9) as K0r; move K0r before pvzI9; clear pvzI9.
set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 45%nat => Z_to_bv 64 (V 45%nat) | 46%nat => Z_to_bv 64 (V 46%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | 48%nat => Z_to_bv 64 (V 48%nat) | 49%nat => Z_to_bv 64 (V 49%nat) | _ => getr R (reg j) end) (fun _ => [])).
set (VzN := (fun j : nat => match j with 2%nat => (V 2%nat) | 43%nat => (V 43%nat) | 44%nat => (V 44%nat) | 45%nat => (V 45%nat) | 46%nat => (V 46%nat) | 47%nat => (V 47%nat) | 48%nat => (V 48%nat) | 49%nat => (V 49%nat) | _ => bv_unsigned (getr R (reg j)) end)).
assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
{ unfold VzN. BigLinkZA.za_tac0 50%nat. }
assert (HR: regs_ok E LibSegJa_ardZ.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl LibSegJa_ardZ.regs0 nth]. apc_norm. repeat split; slotP ZA. }
assert (HK: know_ok RSEGS E M LibSegJa_ardZ.kn0).
{ unfold know_ok, LibSegJa_ardZ.kn0.
apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K3]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K4]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K5]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K6]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K7]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K8]. }
apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K9]. }
apply Forall_nil. }
pvz_hg ltac:(idtac; destruct (LibSegJa_ardZ.seg_sound_ax HFILL HCOPY HTLS fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
change LibSegJa_ardZ.NX0 with 60%nat in Hag.
exists fx', R', M'. pvz_linconj. split. exact Hgr.
assert (FRW: forall a : word, M' a = M a).
{ intros a. apply Hfr. unfold LibSegJa_ardZ.F0.
apply L5K.outside_nil_e. }
split. exact FRW.
split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
apply L5K.nth_error_single in Hnth. subst ps.
change (SR.ps_pc LibSegJa_ardZ.ps0) with 0xab378 in Hms. change (SR.ps_regs LibSegJa_ardZ.ps0) with (map (fun i => (i, nth i LibSegJa_ardZ.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
change (SR.ps_cells LibSegJa_ardZ.ps0) with LibSegJa_ardZ.cells0 in Hcells.
split. { exact Hms. }
split. { intros j Hj. apply (BG.kept_regs E E' R R' LibSegJa_ardZ.regs0 LibSegJa_ardZ.regs_out0 60 KS_ardZ KS_ardZ_ok HR Hag Hregs j Hj). }
split. { rewrite (BG.out_reg LibSegJa_ardZ.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth LibSegJa_ardZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { rewrite (BG.out_reg LibSegJa_ardZ.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth LibSegJa_ardZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { rewrite (BG.out_reg LibSegJa_ardZ.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth LibSegJa_ardZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { rewrite (BG.out_reg LibSegJa_ardZ.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth LibSegJa_ardZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { rewrite (BG.out_reg LibSegJa_ardZ.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth LibSegJa_ardZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { rewrite (BG.out_reg LibSegJa_ardZ.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth LibSegJa_ardZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
split. { rewrite (BG.out_reg LibSegJa_ardZ.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth LibSegJa_ardZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
rewrite (BG.out_reg LibSegJa_ardZ.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth LibSegJa_ardZ.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.
End PMARDP.
