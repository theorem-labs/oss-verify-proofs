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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require LibSegBa_azdA_b LibSegBa_azdB_b LibSegBa_azsA_b LibSegBa_azsB_b LibSegBa_azcl_b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNAANP.
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
Module PazdA := LibSegBa_azdA_b.
Definition KS_azdA : list nat := Eval vm_compute in (BG.kept_list 60 PazdA.regs0 PazdA.regs_out0).
Lemma KS_azdA_ok : BG.kept_ok 60 PazdA.regs0 PazdA.regs_out0 KS_azdA = true. Proof. vm_compute. reflexivity. Qed.
Lemma azdA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5.img_clear M 1249280 1282048 ->
  L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 6905856 <= (V 33%nat) <= 140737488355295 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) -> (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) ->
  L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + (V 37%nat)) -> L5.u64_at RSEGS M ((V 33%nat) + 16) (V 41%nat) -> 4096 <= (V 36%nat) <= 140737488355288 ->
  aligned (V 36%nat) 16 -> 0 <= (V 37%nat) <= 81920 -> aligned (V 37%nat) 8 -> 4136 <= (V 41%nat) <= 140737488355327 ->
  0 <= ((V 41%nat) - ((V 36%nat) + (V 37%nat))) <= 81920 -> 0 <= ((V 41%nat) - (V 36%nat)) <= 163840 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 32) <= bv_unsigned a < ((V 2%nat) - 32) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 32) <= i < ((V 2%nat) - 32) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xab7e0 M) (st fx' R' 0x7ba7c M')
        /\ (forall x, In x KS_azdA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 702564
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 16)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 36%nat) + (V 37%nat))
        /\ getr R' (reg 13) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 16) = Z_to_bv 64 (((V 33%nat) + 16) / 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G10 pvzI6 K1 K2 K3 K4 K5 pvzI7 K7 K8 K9 K10 K11 K12 K13 K14 pvzI8 K16 pvzI9 K18 pvzI10 pvzI11 pvzI12.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV41l; move HV41l before pvzI5; pose proof (proj2 pvzI5) as HV41r; move HV41r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K6l; move K6l before pvzI7; pose proof (proj2 pvzI7) as K6r; move K6r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K15l; move K15l before pvzI8; pose proof (proj2 pvzI8) as K15r; move K15r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K17l; move K17l before pvzI9; pose proof (proj2 pvzI9) as K17r; move K17r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K19l; move K19l before pvzI10; pose proof (proj2 pvzI10) as K19r; move K19r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K20l; move K20l before pvzI11; pose proof (proj2 pvzI11) as K20r; move K20r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K21l; move K21l before pvzI12; pose proof (proj2 pvzI12) as K21r; move K21r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_41 := V 41%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 41%nat => Z_to_bv 64 vz_41 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 36%nat => vz_36 | 37%nat => vz_37 | 41%nat => vz_41 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E PazdA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PazdA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PazdA.kn0).
  { unfold know_ok, PazdA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10 K11) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10 K11) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10 K11) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10 K11) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K10 K11; lia | clear - HV33l HV33r K6l K6r K8 K10 K11; lia | clear - HV33l HV33r K6l K6r K8 K10 K11; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10 K11) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10 K11) | evalEk ZA ltac:(clear - HV36l HV36r K15l K15r K20l K20r K21l K21r) | clear - HV33l HV33r K6l K6r K8 K10 K11; lia | clear - HV33l HV33r K6l K6r K8 K10 K11; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10 K11) | evalEk ZA ltac:(clear - HV36l HV36r K15l K15r K20l K20r K21l K21r HV37l HV37r K17l K17r) | clear - HV33l HV33r K6l K6r K8 K10 K11; lia | clear - HV33l HV33r K6l K6r K8 K10 K11; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10 K11) | evalEk ZA ltac:(clear - HV41l HV41r K19l K19r K20l K20r K21l K21r) | clear - HV33l HV33r K6l K6r K8 K10 K11; lia | clear - HV33l HV33r K6l K6r K8 K10 K11; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K15l K15r K20l K20r K21l K21r) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K15l K15r K20l K20r K21l K21r) | clear; lia | exact K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K17l K17r K20l K20r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K17l K17r K20l K20r) | clear; lia | exact K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K19l K19r K20l K20r K21l K21r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K15l K15r K20l K20r K21l K21r HV37l HV37r K17l K17r HV41l HV41r K19l K19r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K15l K15r K20l K20r K21l K21r HV41l HV41r K19l K19r) | exact (conj K21l K21r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PazdA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PazdA.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 32) <= bv_unsigned a < (vz_2 - 32) + 32) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PazdA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K10 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PazdA.ps0) with 0x7ba7c in Hms. change (SR.ps_regs PazdA.ps0) with (map (fun i => (i, nth i PazdA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PazdA.ps0) with PazdA.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PazdA.regs0 PazdA.regs_out0 60 KS_azdA KS_azdA_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PazdA.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PazdA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazdA.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PazdA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazdA.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PazdA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazdA.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PazdA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazdA.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PazdA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazdA.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PazdA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazdA.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PazdA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazdA.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PazdA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazdA.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PazdA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazdB := LibSegBa_azdB_b.
Definition KS_azdB : list nat := Eval vm_compute in (BG.kept_list 60 PazdB.regs0 PazdB.regs_out0).
Lemma KS_azdB_ok : BG.kept_ok 60 PazdB.regs0 PazdB.regs_out0 KS_azdB = true. Proof. vm_compute. reflexivity. Qed.
Lemma azdB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 16) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xab864 M) (st fx' R' 0xab870 M')
        /\ (forall x, In x KS_azdB -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 44%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 pvzI4 K1 K2 K3 K4.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV43l; move HV43l before pvzI2; pose proof (proj2 pvzI2) as HV43r; move HV43r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV44l; move HV44l before pvzI3; pose proof (proj2 pvzI3) as HV44r; move HV44r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4.
  set (vz_2 := V 2%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 43%nat => vz_43 | 44%nat => vz_44 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 45%nat. }
  assert (HR: regs_ok E PazdB.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PazdB.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PazdB.kn0).
  { unfold know_ok, PazdB.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K4]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PazdB.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PazdB.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PazdB.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PazdB.ps0) with 0xab870 in Hms. change (SR.ps_regs PazdB.ps0) with (map (fun i => (i, nth i PazdB.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PazdB.ps0) with PazdB.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PazdB.regs0 PazdB.regs_out0 60 KS_azdB KS_azdB_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PazdB.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PazdB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazdB.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PazdB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PazdB.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PazdB.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazsA := LibSegBa_azsA_b.
Definition KS_azsA : list nat := Eval vm_compute in (BG.kept_list 60 PazsA.regs0 PazsA.regs_out0).
Lemma KS_azsA_ok : BG.kept_ok 60 PazsA.regs0 PazsA.regs_out0 KS_azsA = true. Proof. vm_compute. reflexivity. Qed.
Lemma azsA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5.img_clear M 1249280 1282048 ->
  L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 6905856 <= (V 33%nat) <= 140737488355295 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) -> (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) ->
  L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + (V 37%nat)) -> L5.u64_at RSEGS M ((V 33%nat) + 16) (V 41%nat) -> 4096 <= (V 36%nat) <= 140737488355288 ->
  aligned (V 36%nat) 16 -> 0 <= (V 37%nat) <= 81920 -> aligned (V 37%nat) 8 -> 4136 <= (V 41%nat) <= 140737488355327 ->
  0 <= ((V 41%nat) - ((V 36%nat) + (V 37%nat))) <= 81920 -> 0 <= (V 34%nat) <= 2048 -> 0 <= ((V 41%nat) - (V 36%nat)) <= 163840 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 32) <= bv_unsigned a < ((V 2%nat) - 32) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 32) <= i < ((V 2%nat) - 32) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xab89c M) (st fx' R' 0x7ba7c M')
        /\ (forall x, In x KS_azsA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 702760
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 16)
        /\ getr R' (reg 5) = Z_to_bv 64 0
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 ((40 * (V 34%nat)) + (V 36%nat))
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 36%nat) + (V 37%nat))
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 16) = Z_to_bv 64 (((V 33%nat) + 8) / 8)
        /\ getr R' (reg 17) = Z_to_bv 64 (40 * (V 34%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G10 G11 pvzI7 K1 K2 K3 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 K14 pvzI9 K16 pvzI10 K18 pvzI11 pvzI12 pvzI13 pvzI14.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV41l; move HV41l before pvzI6; pose proof (proj2 pvzI6) as HV41r; move HV41r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K15l; move K15l before pvzI9; pose proof (proj2 pvzI9) as K15r; move K15r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K17l; move K17l before pvzI10; pose proof (proj2 pvzI10) as K17r; move K17r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K19l; move K19l before pvzI11; pose proof (proj2 pvzI11) as K19r; move K19r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K20l; move K20l before pvzI12; pose proof (proj2 pvzI12) as K20r; move K20r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K21l; move K21l before pvzI13; pose proof (proj2 pvzI13) as K21r; move K21r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K22l; move K22l before pvzI14; pose proof (proj2 pvzI14) as K22r; move K22r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_41 := V 41%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 41%nat => Z_to_bv 64 vz_41 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 37%nat => vz_37 | 41%nat => vz_41 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E PazsA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PazsA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PazsA.kn0).
  { unfold know_ok, PazsA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10 K11) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10 K11) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10 K11) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10 K11) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K10 K11; lia | clear - HV33l HV33r K6l K6r K8 K10 K11; lia | clear - HV33l HV33r K6l K6r K8 K10 K11; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10 K11) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10 K11) | evalEk ZA ltac:(clear - HV36l HV36r K15l K15r K20l K20r K22l K22r) | clear - HV33l HV33r K6l K6r K8 K10 K11; lia | clear - HV33l HV33r K6l K6r K8 K10 K11; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10 K11) | evalEk ZA ltac:(clear - HV36l HV36r K15l K15r K20l K20r K22l K22r HV37l HV37r K17l K17r) | clear - HV33l HV33r K6l K6r K8 K10 K11; lia | clear - HV33l HV33r K6l K6r K8 K10 K11; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10 K11) | evalEk ZA ltac:(clear - HV41l HV41r K19l K19r K20l K20r K22l K22r) | clear - HV33l HV33r K6l K6r K8 K10 K11; lia | clear - HV33l HV33r K6l K6r K8 K10 K11; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K15l K15r K20l K20r K22l K22r) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K15l K15r K20l K20r K22l K22r) | clear; lia | exact K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K17l K17r K20l K20r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K17l K17r K20l K20r) | clear; lia | exact K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K19l K19r K20l K20r K22l K22r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K15l K15r K20l K20r K22l K22r HV37l HV37r K17l K17r HV41l HV41r K19l K19r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K15l K15r K20l K20r K22l K22r HV41l HV41r K19l K19r) | exact (conj K22l K22r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PazsA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PazsA.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 32) <= bv_unsigned a < (vz_2 - 32) + 32) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PazsA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K10 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PazsA.ps0) with 0x7ba7c in Hms. change (SR.ps_regs PazsA.ps0) with (map (fun i => (i, nth i PazsA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PazsA.ps0) with PazsA.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PazsA.regs0 PazsA.regs_out0 60 KS_azsA KS_azsA_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PazsA.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PazsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazsA.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PazsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazsA.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PazsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazsA.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PazsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazsA.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PazsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazsA.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PazsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazsA.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PazsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazsA.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PazsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazsA.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PazsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazsA.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PazsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazsA.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PazsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazsB := LibSegBa_azsB_b.
Definition KS_azsB : list nat := Eval vm_compute in (BG.kept_list 60 PazsB.regs0 PazsB.regs_out0).
Lemma KS_azsB_ok : BG.kept_ok 60 PazsB.regs0 PazsB.regs_out0 KS_azsB = true. Proof. vm_compute. reflexivity. Qed.
Lemma azsB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 16) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xab928 M) (st fx' R' 0xab934 M')
        /\ (forall x, In x KS_azsB -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 44%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 pvzI4 K1 K2 K3 K4.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV43l; move HV43l before pvzI2; pose proof (proj2 pvzI2) as HV43r; move HV43r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV44l; move HV44l before pvzI3; pose proof (proj2 pvzI3) as HV44r; move HV44r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4.
  set (vz_2 := V 2%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 43%nat => vz_43 | 44%nat => vz_44 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 45%nat. }
  assert (HR: regs_ok E PazsB.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PazsB.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PazsB.kn0).
  { unfold know_ok, PazsB.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K4]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PazsB.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PazsB.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PazsB.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PazsB.ps0) with 0xab934 in Hms. change (SR.ps_regs PazsB.ps0) with (map (fun i => (i, nth i PazsB.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PazsB.ps0) with PazsB.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PazsB.regs0 PazsB.regs_out0 60 KS_azsB KS_azsB_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PazsB.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PazsB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazsB.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PazsB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PazsB.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PazsB.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.
(* [comment removed for export] *)

Module Pazcl := LibSegBa_azcl_b.
Definition KS_azcl_0 : list nat := Eval vm_compute in (BG.kept_list 60 Pazcl.regs0 Pazcl.regs_out0).
Lemma KS_azcl_0_ok : BG.kept_ok 60 Pazcl.regs0 Pazcl.regs_out0 KS_azcl_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_azcl_1 : list nat := Eval vm_compute in (BG.kept_list 60 Pazcl.regs0 Pazcl.regs_out1).
Lemma KS_azcl_1_ok : BG.kept_ok 60 Pazcl.regs0 Pazcl.regs_out1 KS_azcl_1 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma azcl_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5.u64_at RSEGS M 1309752 2147450880 ->
  L5.u32_at RSEGS M 1309760 1 -> 6905856 <= (V 33%nat) <= 140737488355295 -> aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) ->
  L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) -> (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) ->
  L5.u64_at RSEGS M ((V 33%nat) + 16) (V 41%nat) -> 4096 <= (V 36%nat) <= 140737488355288 -> aligned (V 36%nat) 16 -> 4136 <= (V 41%nat) <= 140737488355327 ->
  L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + (40 * (V 39%nat))) -> 0 <= (V 39%nat) <= 2048 -> 0 <= (((-1) * (V 36%nat)) + (((-40) * (V 39%nat)) + (V 41%nat))) <= 81920 -> L5.img_clear M 65536 1282048 ->
  L5.writable RSEGS M ((V 33%nat) + 8) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 16) -> ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 16) <= i < ((V 2%nat) - 16) + 16) -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xab740 M) (st fx' R' 0xab89c M')
        /\ (forall x, In x KS_azcl_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 39%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 40
        /\ getr R' (reg 16) = Z_to_bv 64 (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) (V 36%nat)
        /\ 1 <= (V 39%nat) <= 2048)
      \/ (msteps RSEGS (st fx R 0xab740 M) (st fx' R' 0xab89c M')
        /\ (forall x, In x KS_azcl_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) (V 36%nat)
        /\ 0 <= (V 39%nat) <= 0)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G10 pvzI6 K1 K2 K3 K4 pvzI7 K6 K7 K8 K9 K10 K11 K12 pvzI8 K14 pvzI9 K16 pvzI10 pvzI11 K19 K20.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV39l; move HV39l before pvzI4; pose proof (proj2 pvzI4) as HV39r; move HV39r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV41l; move HV41l before pvzI5; pose proof (proj2 pvzI5) as HV41r; move HV41r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K5l; move K5l before pvzI7; pose proof (proj2 pvzI7) as K5r; move K5r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K13l; move K13l before pvzI8; pose proof (proj2 pvzI8) as K13r; move K13r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K15l; move K15l before pvzI9; pose proof (proj2 pvzI9) as K15r; move K15r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K17l; move K17l before pvzI10; pose proof (proj2 pvzI10) as K17r; move K17r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K18l; move K18l before pvzI11; pose proof (proj2 pvzI11) as K18r; move K18r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_41 := V 41%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 36%nat => Z_to_bv 64 vz_36 | 39%nat => Z_to_bv 64 vz_39 | 41%nat => Z_to_bv 64 vz_41 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 36%nat => vz_36 | 39%nat => vz_39 | 41%nat => vz_41 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E Pazcl.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pazcl.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pazcl.kn0).
  { unfold know_ok, Pazcl.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7 K9 K10) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7 K9 K10) | clear; lia | exact K6]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7 K9 K10) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7 K9 K10) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K5l K5r K7 K9 K10; lia | clear - HV33l HV33r K5l K5r K7 K9 K10; lia | clear - HV33l HV33r K5l K5r K7 K9 K10; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7 K9 K10) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7 K9 K10) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7 K9 K10) | evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K18l K18r) | clear - HV33l HV33r K5l K5r K7 K9 K10; lia | clear - HV33l HV33r K5l K5r K7 K9 K10; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7 K9 K10) | evalEk ZA ltac:(clear - HV41l HV41r K15l K15r K18l K18r) | clear - HV33l HV33r K5l K5r K7 K9 K10; lia | clear - HV33l HV33r K5l K5r K7 K9 K10; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K18l K18r) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K18l K18r) | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K15l K15r K18l K18r) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7 K9 K10) | evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K18l K18r HV39l HV39r K17l K17r) | clear - HV33l HV33r K5l K5r K7 K9 K10; lia | clear - HV33l HV33r K5l K5r K7 K9 K10; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K17l K17r K18l K18r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K18l K18r HV39l HV39r K17l K17r HV41l HV41r K15l K15r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7 K9 K10) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K5l K5r K7 K9 K10; lia | clear - HV33l HV33r K5l K5r K7 K9 K10; lia | clear - HV33l HV33r K5l K5r K7 K9 K10; lia | exactA K20]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pazcl.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pazcl.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 16) <= bv_unsigned a < (vz_2 - 16) + 16) -> ~ ((vz_33 + 8) <= bv_unsigned a < (vz_33 + 8) + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold Pazcl.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K9 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K5l K5r K7 K9 K10) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K5l K5r K7 K9 K10 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc Pazcl.ps0) with 0xab89c in Hms. change (SR.ps_regs Pazcl.ps0) with (map (fun i => (i, nth i Pazcl.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pazcl.ps0) with Pazcl.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pazcl.regs0 Pazcl.regs_out0 60 KS_azcl_0 KS_azcl_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pazcl.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pazcl.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E. cbn [edenot ev].
      rewrite BG.md_mul_lit.
      assert (SR3 : alu64 ALU_SRA (Z_to_bv 64 (40 * vz_39)) (Z_to_bv 64 3) = Z_to_bv 64 (5 * vz_39)).
      { apply bv_eq. rewrite u_sra64_nonneg by (rewrite BG.unsigned_lit by lia; lia). rewrite !BG.unsigned_lit by lia. change (3 mod 64) with 3.
        replace (40 * vz_39) with (5 * vz_39 * 2 ^ 3) by lia. rewrite Z.div_mul by lia. reflexivity. }
      rewrite SR3, BG.md_mul_lit. replace (-3689348814741910323 * (5 * vz_39)) with (vz_39 + (- vz_39) * 2 ^ 64) by lia.
      rewrite <- Z_to_bv64_mod, Z.mod_add by lia. rewrite Z_to_bv64_mod. reflexivity. }
    split. { rewrite (BG.out_reg Pazcl.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pazcl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pazcl.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pazcl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pazcl.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth Pazcl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pazcl.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth Pazcl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K5l K5r K7 K9 K10) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K13l K13r K18l K18r) | clear; lia]. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV39l HV39r K17l K17r K18l K18r)]. 
  - right.
    change (SR.ps_pc Pazcl.ps1) with 0xab89c in Hms. change (SR.ps_regs Pazcl.ps1) with (map (fun i => (i, nth i Pazcl.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pazcl.ps1) with Pazcl.cells1 in Hcells. unfold Pazcl.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pazcl.regs0 Pazcl.regs_out1 60 KS_azcl_1 KS_azcl_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pazcl.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth Pazcl.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pazcl.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth Pazcl.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pazcl.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth Pazcl.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pazcl.regs_out1 E' R' 14 Hregs) by (clear; lia). cbn [nth Pazcl.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K5l K5r K7 K9 K10) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K13l K13r K18l K18r) | clear; lia]. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV39l HV39r K17l K17r K18l K18r)]. 
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

End PNAANP.
