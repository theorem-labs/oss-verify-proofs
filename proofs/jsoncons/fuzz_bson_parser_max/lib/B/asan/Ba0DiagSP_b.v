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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require LibSegBa_sC1_b LibSegBa_sC3_b LibSegBa_sC4_b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module AS0DIAGSP.
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
Module PsC1 := LibSegBa_sC1_b.
Definition KS_sC1 : list nat := Eval vm_compute in (BG.kept_list 140 PsC1.regs0 PsC1.regs_out0).
Lemma KS_sC1_ok : BG.kept_ok 140 PsC1.regs0 PsC1.regs_out0 KS_sC1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma sC1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 1186016 -> getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 2147483647 ->
  140735332552704 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4320) 4320 -> L5.defined M ((V 2%nat) - 4320) 4320 ->
  L5.img_clear M 65536 1282048 -> 140735332552704 <= (V 33%nat) <= 140737488355311 -> 0 <= (V 34%nat) <= 131071 -> (((V 2%nat) - 4320) + 4320 <= (V 33%nat) \/ (V 33%nat) + ((V 34%nat) + 1) <= ((V 2%nat) - 4320)) ->
  L5.u8_at RSEGS M 1313048 1 -> L5.u64_at RSEGS M 1283192 1221668 -> L5.u64_at RSEGS M 1282824 1218564 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 4320) <= bv_unsigned a < ((V 2%nat) - 4320) + 4320) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 4320) <= i < ((V 2%nat) - 4320) + 4320) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x63370 M) (st fx' R' 0x129804 M')
        /\ (forall x, In x KS_sC1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 413824
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 4304)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 2176)
        /\ getr R' (reg 9) = Z_to_bv 64 2147483647
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 2147483647
        /\ getr R' (reg 13) = Z_to_bv 64 1218564
        /\ getr R' (reg 18) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 0
        /\ getr R' (reg 20) = Z_to_bv 64 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 2232) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 2224) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 2216) 2147483647
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 2208) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 2200) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 2192) 2147483647
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 2184) 1221704
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 2168) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 2160) (V 2%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 2152) 407348
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) 1186016
        /\ L5.defined M' ((V 2%nat) - 4304) 2072
        /\ L5.defined M' ((V 2%nat) - 2176) 8
        /\ L5.defined M' ((V 2%nat) - 2144) 2080).
Proof.
  intros pvzI1 pvzI2 pvzI3 G1 G2 G10 G11 pvzI4 K1 K2 K3 K4 pvzI5 pvzI6 K7 K8 K9 K10.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K5l; move K5l before pvzI5; pose proof (proj2 pvzI5) as K5r; move K5r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K6l; move K6l before pvzI6; pose proof (proj2 pvzI6) as K6r; move K6r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 35%nat. }
  assert (HR: regs_ok E PsC1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PsC1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PsC1.kn0).
  { unfold know_ok, PsC1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K10]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PsC1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PsC1.NX0 with 140%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 4320) <= bv_unsigned a < (vz_2 - 4320) + 4320) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PsC1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K7 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PsC1.ps0) with 0x129804 in Hms. change (SR.ps_regs PsC1.ps0) with (map (fun i => (i, nth i PsC1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PsC1.ps0) with PsC1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PsC1.regs0 PsC1.regs_out0 140 KS_sC1 KS_sC1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PsC1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PsC1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsC1.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PsC1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsC1.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PsC1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsC1.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PsC1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsC1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PsC1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsC1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PsC1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsC1.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PsC1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsC1.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PsC1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsC1.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PsC1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsC1.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PsC1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K5l K5r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K5l K5r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 18); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 19); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 20); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PsC3 := LibSegBa_sC3_b.
Definition KS_sC3 : list nat := Eval vm_compute in (BG.kept_list 140 PsC3.regs0 PsC3.regs_out0).
Lemma KS_sC3_ok : BG.kept_ok 140 PsC3.regs0 PsC3.regs_out0 KS_sC3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma sC3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 20%nat) < 2 ^ 64 -> 0 <= (V 21%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 120%nat) < 2 ^ 64 -> 0 <= (V 121%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 ((V 33%nat) + (V 34%nat)) -> getr R (reg 20) = Z_to_bv 64 (V 120%nat) -> getr R (reg 21) = Z_to_bv 64 (V 121%nat) ->
  140735332552704 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 16) 16 -> L5.defined M ((V 2%nat) - 16) 16 ->
  L5.img_clear M 65536 1282048 -> 140735332552704 <= (V 33%nat) <= 140737488355311 -> 0 <= (V 34%nat) <= 131071 -> (((V 2%nat) - 16) + 16 <= (V 33%nat) \/ (V 33%nat) + ((V 34%nat) + 1) <= ((V 2%nat) - 16)) ->
  L5.u64_at RSEGS M ((V 2%nat) + 2120) 1221704 -> L5.u64_at RSEGS M ((V 2%nat) + 2112) 2147483647 -> L5.u64_at RSEGS M ((V 2%nat) + 2104) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 2096) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 2088) 2147483647 -> L5.u64_at RSEGS M ((V 2%nat) + 2080) (V 20%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 2072) (V 21%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 2152) 407348 ->
  L5.u64_at RSEGS M ((V 2%nat) + 2144) ((V 2%nat) + 4304) -> L5.u64_at RSEGS M ((V 2%nat) + 2136) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 16) <= i < ((V 2%nat) - 16) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x650e0 M) (st fx' R' 0x63734 M')
        /\ (forall x, In x KS_sC3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 407348
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) + 2160)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) + 4304)
        /\ getr R' (reg 9) = Z_to_bv 64 1
        /\ getr R' (reg 10) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 2147483647
        /\ getr R' (reg 20) = Z_to_bv 64 (V 20%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 21%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G10 G20 G21 pvzI8 K1 K2 K3 K4 pvzI9 pvzI10 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV20l; move HV20l before pvzI2; pose proof (proj2 pvzI2) as HV20r; move HV20r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV21l; move HV21l before pvzI3; pose proof (proj2 pvzI3) as HV21r; move HV21r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV33l; move HV33l before pvzI4; pose proof (proj2 pvzI4) as HV33r; move HV33r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV34l; move HV34l before pvzI5; pose proof (proj2 pvzI5) as HV34r; move HV34r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV120l; move HV120l before pvzI6; pose proof (proj2 pvzI6) as HV120r; move HV120r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV121l; move HV121l before pvzI7; pose proof (proj2 pvzI7) as HV121r; move HV121r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K5l; move K5l before pvzI9; pose proof (proj2 pvzI9) as K5r; move K5r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_20 := V 20%nat) in *. set (vz_21 := V 21%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_120 := V 120%nat) in *. set (vz_121 := V 121%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 20%nat => Z_to_bv 64 vz_20 | 21%nat => Z_to_bv 64 vz_21 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 120%nat => Z_to_bv 64 vz_120 | 121%nat => Z_to_bv 64 vz_121 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 20%nat => vz_20 | 21%nat => vz_21 | 33%nat => vz_33 | 34%nat => vz_34 | 120%nat => vz_120 | 121%nat => vz_121 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 122%nat. }
  assert (HR: regs_ok E PsC3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PsC3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PsC3.kn0).
  { unfold know_ok, PsC3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV20l HV20r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV21l HV21r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K17]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PsC3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PsC3.NX0 with 140%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 16) <= bv_unsigned a < (vz_2 - 16) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PsC3.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K7 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PsC3.ps0) with 0x63734 in Hms. change (SR.ps_regs PsC3.ps0) with (map (fun i => (i, nth i PsC3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PsC3.ps0) with PsC3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PsC3.regs0 PsC3.regs_out0 140 KS_sC3 KS_sC3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PsC3.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PsC3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsC3.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PsC3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsC3.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PsC3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsC3.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PsC3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsC3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PsC3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsC3.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PsC3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsC3.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PsC3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsC3.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PsC3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PsC3.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PsC3.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PsC4 := LibSegBa_sC4_b.
Definition KS_sC4 : list nat := Eval vm_compute in (BG.kept_list 140 PsC4.regs0 PsC4.regs_out0).
Lemma KS_sC4_ok : BG.kept_ok 140 PsC4.regs0 PsC4.regs_out0 KS_sC4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma sC4_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 8%nat) < 2 ^ 64 -> 0 <= (V 9%nat) < 2 ^ 64 -> 0 <= (V 18%nat) < 2 ^ 64 -> 0 <= (V 19%nat) < 2 ^ 64 -> 0 <= (V 20%nat) < 2 ^ 64 -> 0 <= (V 21%nat) < 2 ^ 64 -> 0 <= (V 22%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 108%nat) < 2 ^ 64 -> 0 <= (V 109%nat) < 2 ^ 64 -> 0 <= (V 118%nat) < 2 ^ 64 -> 0 <= (V 119%nat) < 2 ^ 64 -> 0 <= (V 120%nat) < 2 ^ 64 -> 0 <= (V 121%nat) < 2 ^ 64 -> 0 <= (V 122%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 8) = Z_to_bv 64 (V 108%nat) -> getr R (reg 9) = Z_to_bv 64 (V 109%nat) -> getr R (reg 18) = Z_to_bv 64 (V 118%nat) -> getr R (reg 19) = Z_to_bv 64 (V 119%nat) -> getr R (reg 20) = Z_to_bv 64 (V 120%nat) -> getr R (reg 21) = Z_to_bv 64 (V 121%nat) -> getr R (reg 22) = Z_to_bv 64 (V 122%nat) ->
  140735332552704 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 16) 16 -> L5.defined M ((V 2%nat) - 16) 16 ->
  L5.img_clear M 65536 1282048 -> 140735332552704 <= (V 33%nat) <= 140737488355311 -> 0 <= (V 34%nat) <= 131071 -> (((V 2%nat) - 16) + 16 <= (V 33%nat) \/ (V 33%nat) + ((V 34%nat) + 1) <= ((V 2%nat) - 16)) ->
  L5.u64_at RSEGS M ((V 2%nat) + 2136) 1186016 -> L5.u64_at RSEGS M ((V 2%nat) + 2128) (V 8%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 2120) (V 9%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 2112) (V 18%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 2104) (V 19%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 2096) (V 20%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 2088) (V 21%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 2080) (V 22%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 16) <= i < ((V 2%nat) - 16) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x637a8 M) (st fx' R' 0x1218e0 M')
        /\ (forall x, In x KS_sC4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 1186016
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) + 2144)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 8%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 9%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 18%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 19%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 20%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 21%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 22%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 G2 G8 G9 G18 G19 G20 G21 G22 pvzI18 K1 K2 K3 K4 pvzI19 pvzI20 K7 K8 K9 K10 K11 K12 K13 K14 K15.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV8l; move HV8l before pvzI2; pose proof (proj2 pvzI2) as HV8r; move HV8r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV9l; move HV9l before pvzI3; pose proof (proj2 pvzI3) as HV9r; move HV9r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV18l; move HV18l before pvzI4; pose proof (proj2 pvzI4) as HV18r; move HV18r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV19l; move HV19l before pvzI5; pose proof (proj2 pvzI5) as HV19r; move HV19r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV20l; move HV20l before pvzI6; pose proof (proj2 pvzI6) as HV20r; move HV20r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV21l; move HV21l before pvzI7; pose proof (proj2 pvzI7) as HV21r; move HV21r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV22l; move HV22l before pvzI8; pose proof (proj2 pvzI8) as HV22r; move HV22r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV33l; move HV33l before pvzI9; pose proof (proj2 pvzI9) as HV33r; move HV33r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV34l; move HV34l before pvzI10; pose proof (proj2 pvzI10) as HV34r; move HV34r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV108l; move HV108l before pvzI11; pose proof (proj2 pvzI11) as HV108r; move HV108r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV109l; move HV109l before pvzI12; pose proof (proj2 pvzI12) as HV109r; move HV109r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV118l; move HV118l before pvzI13; pose proof (proj2 pvzI13) as HV118r; move HV118r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV119l; move HV119l before pvzI14; pose proof (proj2 pvzI14) as HV119r; move HV119r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV120l; move HV120l before pvzI15; pose proof (proj2 pvzI15) as HV120r; move HV120r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV121l; move HV121l before pvzI16; pose proof (proj2 pvzI16) as HV121r; move HV121r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV122l; move HV122l before pvzI17; pose proof (proj2 pvzI17) as HV122r; move HV122r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K0l; move K0l before pvzI18; pose proof (proj2 pvzI18) as K0r; move K0r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K5l; move K5l before pvzI19; pose proof (proj2 pvzI19) as K5r; move K5r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K6l; move K6l before pvzI20; pose proof (proj2 pvzI20) as K6r; move K6r before pvzI20; clear pvzI20.
  set (vz_2 := V 2%nat) in *. set (vz_8 := V 8%nat) in *. set (vz_9 := V 9%nat) in *. set (vz_18 := V 18%nat) in *. set (vz_19 := V 19%nat) in *. set (vz_20 := V 20%nat) in *. set (vz_21 := V 21%nat) in *. set (vz_22 := V 22%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_108 := V 108%nat) in *. set (vz_109 := V 109%nat) in *. set (vz_118 := V 118%nat) in *. set (vz_119 := V 119%nat) in *. set (vz_120 := V 120%nat) in *. set (vz_121 := V 121%nat) in *. set (vz_122 := V 122%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 8%nat => Z_to_bv 64 vz_8 | 9%nat => Z_to_bv 64 vz_9 | 18%nat => Z_to_bv 64 vz_18 | 19%nat => Z_to_bv 64 vz_19 | 20%nat => Z_to_bv 64 vz_20 | 21%nat => Z_to_bv 64 vz_21 | 22%nat => Z_to_bv 64 vz_22 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 108%nat => Z_to_bv 64 vz_108 | 109%nat => Z_to_bv 64 vz_109 | 118%nat => Z_to_bv 64 vz_118 | 119%nat => Z_to_bv 64 vz_119 | 120%nat => Z_to_bv 64 vz_120 | 121%nat => Z_to_bv 64 vz_121 | 122%nat => Z_to_bv 64 vz_122 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 8%nat => vz_8 | 9%nat => vz_9 | 18%nat => vz_18 | 19%nat => vz_19 | 20%nat => vz_20 | 21%nat => vz_21 | 22%nat => vz_22 | 33%nat => vz_33 | 34%nat => vz_34 | 108%nat => vz_108 | 109%nat => vz_109 | 118%nat => vz_118 | 119%nat => vz_119 | 120%nat => vz_120 | 121%nat => vz_121 | 122%nat => vz_122 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 123%nat. }
  assert (HR: regs_ok E PsC4.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PsC4.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PsC4.kn0).
  { unfold know_ok, PsC4.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV8l HV8r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV9l HV9r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV18l HV18r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV19l HV19r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV20l HV20r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV21l HV21r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV22l HV22r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K15]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PsC4.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PsC4.NX0 with 140%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 16) <= bv_unsigned a < (vz_2 - 16) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PsC4.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K7 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PsC4.ps0) with 0x1218e0 in Hms. change (SR.ps_regs PsC4.ps0) with (map (fun i => (i, nth i PsC4.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PsC4.ps0) with PsC4.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PsC4.regs0 PsC4.regs_out0 140 KS_sC4 KS_sC4_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PsC4.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PsC4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsC4.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PsC4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsC4.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PsC4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsC4.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PsC4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsC4.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PsC4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsC4.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PsC4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsC4.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PsC4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsC4.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PsC4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PsC4.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PsC4.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

End AS0DIAGSP.
