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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require LibSegBa_afbA_b LibSegBa_afbE_b LibSegBa_afbB1_b LibSegBa_afbB2_b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PMAFBP.
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
Module PafbA := LibSegBa_afbA_b.
Definition KS_afbA : list nat := Eval vm_compute in (BG.kept_list 48 PafbA.regs0 PafbA.regs_out0).
Lemma KS_afbA_ok : BG.kept_ok 48 PafbA.regs0 PafbA.regs_out0 KS_afbA = true. Proof. vm_compute. reflexivity. Qed.
Lemma afbA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 16384 ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487216 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 6905856 <= (V 36%nat) <= 140737488355032 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 -> (((V 2%nat) - 48) + 48 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 48)) ->
  6905856 <= (V 37%nat) <= 140737488355056 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 272 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 34 ->
  L5.writable RSEGS M (V 37%nat) 272 -> (((V 2%nat) - 48) + 48 <= (V 37%nat) \/ (V 37%nat) + 272 <= ((V 2%nat) - 48)) -> ((V 36%nat) + 296 <= (V 37%nat) \/ (V 37%nat) + 272 <= (V 36%nat)) -> L5.u64_at RSEGS M ((V 36%nat) + 240) (V 37%nat) ->
  L5.u64_at RSEGS M ((V 36%nat) + 248) ((V 37%nat) + 16) -> L5.u64_at RSEGS M (V 37%nat) 1265968 -> L5.u64_at RSEGS M ((V 37%nat) + 16) 1265728 -> L5.u32_at RSEGS M ((V 37%nat) + 152) 0 ->
  L5.u32_at RSEGS M ((V 37%nat) + 156) 0 -> L5.u64_at RSEGS M ((V 37%nat) + 160) ((V 37%nat) + 16) -> L5KA.zeros_at M 2147609123 1 -> L5KA.zeros_at M 2147609104 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb29f8 M) (st fx' R' 0xda800 M')
        /\ (forall x, In x KS_afbA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 731892
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 36%nat) + 240)
        /\ getr R' (reg 9) = Z_to_bv 64 16384
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 37%nat) + 16)
        /\ getr R' (reg 13) = Z_to_bv 64 894976
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 19) = Z_to_bv 64 2147450880
        /\ getr R' (reg 20) = Z_to_bv 64 ((((V 36%nat) + 240) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G10 G11 G12 K0 K1 K2 pvzI5 K4 K5 pvzI6 K7 K8 K9 K10 K11 pvzI7 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV34l; move HV34l before pvzI2; pose proof (proj2 pvzI2) as HV34r; move HV34r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K3l; move K3l before pvzI5; pose proof (proj2 pvzI5) as K3r; move K3r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K6l; move K6l before pvzI6; pose proof (proj2 pvzI6) as K6r; move K6r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K12l; move K12l before pvzI7; pose proof (proj2 pvzI7) as K12r; move K12r before pvzI7; clear pvzI7.
  set (vz_2 := V 2%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 34%nat => vz_34 | 36%nat => vz_36 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PafbA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PafbA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PafbA.kn0).
  { unfold know_ok, PafbA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K17; lia | clear - HV2l HV2r K3l K3r K11 K17; lia | clear - HV2l HV2r K3l K3r K11 K17; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K18) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K18) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | exactA K25]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K26]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K27]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PafbA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PafbA.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PafbA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K17 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PafbA.ps0) with 0xda800 in Hms. change (SR.ps_regs PafbA.ps0) with (map (fun i => (i, nth i PafbA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PafbA.ps0) with PafbA.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PafbA.regs0 PafbA.regs_out0 48 KS_afbA KS_afbA_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PafbA.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PafbA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafbA.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PafbA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafbA.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PafbA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafbA.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PafbA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafbA.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PafbA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafbA.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PafbA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafbA.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PafbA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafbA.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PafbA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafbA.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PafbA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PafbE := LibSegBa_afbE_b.
Definition KS_afbE : list nat := Eval vm_compute in (BG.kept_list 48 PafbE.regs0 PafbE.regs_out0).
Lemma KS_afbE_ok : BG.kept_ok 48 PafbE.regs0 PafbE.regs_out0 KS_afbE = true. Proof. vm_compute. reflexivity. Qed.
Lemma afbE_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 16384 ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487216 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 6905856 <= (V 36%nat) <= 140737488355032 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 -> (((V 2%nat) - 48) + 48 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 48)) ->
  6905856 <= (V 37%nat) <= 140737488355056 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 272 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 34 ->
  L5.writable RSEGS M (V 37%nat) 272 -> (((V 2%nat) - 48) + 48 <= (V 37%nat) \/ (V 37%nat) + 272 <= ((V 2%nat) - 48)) -> ((V 36%nat) + 296 <= (V 37%nat) \/ (V 37%nat) + 272 <= (V 36%nat)) -> L5.u64_at RSEGS M ((V 36%nat) + 240) (V 37%nat) ->
  L5.u64_at RSEGS M ((V 36%nat) + 248) ((V 37%nat) + 16) -> L5.u64_at RSEGS M (V 37%nat) 1265968 -> L5.u64_at RSEGS M ((V 37%nat) + 16) 1265728 -> L5.u32_at RSEGS M ((V 37%nat) + 152) 2 ->
  L5.u32_at RSEGS M ((V 37%nat) + 156) 0 -> L5.u64_at RSEGS M ((V 37%nat) + 160) ((V 37%nat) + 16) -> L5KA.zeros_at M 2147609123 1 -> L5KA.zeros_at M 2147609104 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb29f8 M) (st fx' R' 0xb2c80 M')
        /\ (forall x, In x KS_afbE -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 2
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G10 G11 G12 K0 K1 K2 pvzI5 K4 K5 pvzI6 K7 K8 K9 K10 K11 pvzI7 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV34l; move HV34l before pvzI2; pose proof (proj2 pvzI2) as HV34r; move HV34r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K3l; move K3l before pvzI5; pose proof (proj2 pvzI5) as K3r; move K3r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K6l; move K6l before pvzI6; pose proof (proj2 pvzI6) as K6r; move K6r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K12l; move K12l before pvzI7; pose proof (proj2 pvzI7) as K12r; move K12r before pvzI7; clear pvzI7.
  set (vz_2 := V 2%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 34%nat => vz_34 | 36%nat => vz_36 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PafbE.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PafbE.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PafbE.kn0).
  { unfold know_ok, PafbE.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K17; lia | clear - HV2l HV2r K3l K3r K11 K17; lia | clear - HV2l HV2r K3l K3r K11 K17; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K18) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K18) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | exactA K25]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K26]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K27]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PafbE.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PafbE.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PafbE.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K17 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PafbE.ps0) with 0xb2c80 in Hms. change (SR.ps_regs PafbE.ps0) with (map (fun i => (i, nth i PafbE.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PafbE.ps0) with PafbE.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PafbE.regs0 PafbE.regs_out0 48 KS_afbE KS_afbE_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PafbE.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PafbE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafbE.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PafbE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafbE.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PafbE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafbE.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PafbE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PafbB1 := LibSegBa_afbB1_b.
Definition KS_afbB1 : list nat := Eval vm_compute in (BG.kept_list 60 PafbB1.regs0 PafbB1.regs_out0).
Lemma KS_afbB1_ok : BG.kept_ok 60 PafbB1.regs0 PafbB1.regs_out0 KS_afbB1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma afbB1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 ((V 36%nat) + 240) -> getr R (reg 9) = Z_to_bv 64 16384 -> getr R (reg 10) = Z_to_bv 64 16384 -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 ((((V 36%nat) + 240) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487216 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 6905856 <= (V 36%nat) <= 140737488355032 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 -> (((V 2%nat) - 48) + 48 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 48)) ->
  6905856 <= (V 37%nat) <= 140737488355056 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 272 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 34 ->
  L5.writable RSEGS M (V 37%nat) 272 -> (((V 2%nat) - 48) + 48 <= (V 37%nat) \/ (V 37%nat) + 272 <= ((V 2%nat) - 48)) -> ((V 36%nat) + 296 <= (V 37%nat) \/ (V 37%nat) + 272 <= (V 36%nat)) -> L5.u64_at RSEGS M ((V 36%nat) + 240) (V 37%nat) ->
  L5.u64_at RSEGS M ((V 36%nat) + 248) ((V 37%nat) + 16) -> L5.u64_at RSEGS M (V 37%nat) 1265968 -> L5.u64_at RSEGS M ((V 37%nat) + 16) 1265728 -> L5.u32_at RSEGS M ((V 37%nat) + 152) 0 ->
  L5.u32_at RSEGS M ((V 37%nat) + 156) 0 -> L5.u64_at RSEGS M ((V 37%nat) + 160) ((V 37%nat) + 16) -> L5KA.zeros_at M 2147609123 1 -> L5KA.zeros_at M 2147609104 1 ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 41%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 43%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 45%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb2af4 M) (st fx' R' 0xb2c80 M')
        /\ (forall x, In x KS_afbB1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 41%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 42%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 45%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G8 G9 G10 G19 G20 K0 K1 K2 pvzI10 K4 K5 pvzI11 K7 K8 K9 K10 K11 pvzI12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV40l; move HV40l before pvzI4; pose proof (proj2 pvzI4) as HV40r; move HV40r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV41l; move HV41l before pvzI5; pose proof (proj2 pvzI5) as HV41r; move HV41r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV42l; move HV42l before pvzI6; pose proof (proj2 pvzI6) as HV42r; move HV42r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV43l; move HV43l before pvzI7; pose proof (proj2 pvzI7) as HV43r; move HV43r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV44l; move HV44l before pvzI8; pose proof (proj2 pvzI8) as HV44r; move HV44r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV45l; move HV45l before pvzI9; pose proof (proj2 pvzI9) as HV45r; move HV45r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K6l; move K6l before pvzI11; pose proof (proj2 pvzI11) as K6r; move K6r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K12l; move K12l before pvzI12; pose proof (proj2 pvzI12) as K12r; move K12r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 40%nat => vz_40 | 41%nat => vz_41 | 42%nat => vz_42 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 46%nat. }
  assert (HR: regs_ok E PafbB1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PafbB1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PafbB1.kn0).
  { unfold know_ok, PafbB1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K17; lia | clear - HV2l HV2r K3l K3r K11 K17; lia | clear - HV2l HV2r K3l K3r K11 K17; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K18) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K18) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | exactA K25]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K26]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K3l K3r K11 K17; lia | clear - HV2l HV2r K3l K3r K11 K17; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear - HV41l HV41r) | clear - HV2l HV2r K3l K3r K11 K17; lia | clear - HV2l HV2r K3l K3r K11 K17; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV2l HV2r K3l K3r K11 K17; lia | clear - HV2l HV2r K3l K3r K11 K17; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K3l K3r K11 K17; lia | clear - HV2l HV2r K3l K3r K11 K17; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K3l K3r K11 K17; lia | clear - HV2l HV2r K3l K3r K11 K17; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K3l K3r K11 K17; lia | clear - HV2l HV2r K3l K3r K11 K17; lia | exactA K33]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PafbB1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PafbB1.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PafbB1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K17 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PafbB1.ps0) with 0xb2c80 in Hms. change (SR.ps_regs PafbB1.ps0) with (map (fun i => (i, nth i PafbB1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PafbB1.ps0) with PafbB1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PafbB1.regs0 PafbB1.regs_out0 60 KS_afbB1 KS_afbB1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PafbB1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PafbB1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafbB1.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PafbB1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafbB1.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PafbB1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafbB1.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PafbB1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafbB1.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PafbB1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafbB1.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PafbB1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafbB1.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PafbB1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear - HV41l HV41r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear - HV42l HV42r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PafbB2 := LibSegBa_afbB2_b.
Definition KS_afbB2 : list nat := Eval vm_compute in (BG.kept_list 60 PafbB2.regs0 PafbB2.regs_out0).
Lemma KS_afbB2_ok : BG.kept_ok 60 PafbB2.regs0 PafbB2.regs_out0 KS_afbB2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma afbB2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 ((V 36%nat) + 240) -> getr R (reg 9) = Z_to_bv 64 16384 -> getr R (reg 10) = Z_to_bv 64 (V 35%nat) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 ((((V 36%nat) + 240) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487216 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 6905856 <= (V 36%nat) <= 140737488355032 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 -> (((V 2%nat) - 48) + 48 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 48)) ->
  6905856 <= (V 37%nat) <= 140737488355056 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 272 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 34 ->
  L5.writable RSEGS M (V 37%nat) 272 -> (((V 2%nat) - 48) + 48 <= (V 37%nat) \/ (V 37%nat) + 272 <= ((V 2%nat) - 48)) -> ((V 36%nat) + 296 <= (V 37%nat) \/ (V 37%nat) + 272 <= (V 36%nat)) -> L5.u64_at RSEGS M ((V 36%nat) + 240) (V 37%nat) ->
  L5.u64_at RSEGS M ((V 36%nat) + 248) ((V 37%nat) + 16) -> L5.u64_at RSEGS M (V 37%nat) 1265968 -> L5.u64_at RSEGS M ((V 37%nat) + 16) 1265728 -> L5.u32_at RSEGS M ((V 37%nat) + 152) 0 ->
  L5.u32_at RSEGS M ((V 37%nat) + 156) 0 -> L5.u64_at RSEGS M ((V 37%nat) + 160) ((V 37%nat) + 16) -> L5KA.zeros_at M 2147609123 1 -> L5KA.zeros_at M 2147609104 1 ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 41%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 43%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 45%nat) -> 0 <= (V 35%nat) <= 16383 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> ~ (((V 37%nat) + 152) <= bv_unsigned a < ((V 37%nat) + 152) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> ~ (((V 37%nat) + 152) <= i < ((V 37%nat) + 152) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb2af4 M) (st fx' R' 0xb2c80 M')
        /\ (forall x, In x KS_afbB2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 45%nat)
        /\ L5.u32_at RSEGS M' ((V 37%nat) + 152) 2
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 41%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 42%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 45%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 G2 G8 G9 G10 G19 G20 K0 K1 K2 pvzI11 K4 K5 pvzI12 K7 K8 K9 K10 K11 pvzI13 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 pvzI14.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV35l; move HV35l before pvzI2; pose proof (proj2 pvzI2) as HV35r; move HV35r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV40l; move HV40l before pvzI5; pose proof (proj2 pvzI5) as HV40r; move HV40r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV41l; move HV41l before pvzI6; pose proof (proj2 pvzI6) as HV41r; move HV41r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV42l; move HV42l before pvzI7; pose proof (proj2 pvzI7) as HV42r; move HV42r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV43l; move HV43l before pvzI8; pose proof (proj2 pvzI8) as HV43r; move HV43r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV44l; move HV44l before pvzI9; pose proof (proj2 pvzI9) as HV44r; move HV44r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV45l; move HV45l before pvzI10; pose proof (proj2 pvzI10) as HV45r; move HV45r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K3l; move K3l before pvzI11; pose proof (proj2 pvzI11) as K3r; move K3r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K6l; move K6l before pvzI12; pose proof (proj2 pvzI12) as K6r; move K6r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K12l; move K12l before pvzI13; pose proof (proj2 pvzI13) as K12r; move K12r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K34l; move K34l before pvzI14; pose proof (proj2 pvzI14) as K34r; move K34r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 40%nat => vz_40 | 41%nat => vz_41 | 42%nat => vz_42 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 46%nat. }
  assert (HR: regs_ok E PafbB2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PafbB2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PafbB2.kn0).
  { unfold know_ok, PafbB2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K17; lia | clear - HV2l HV2r K3l K3r K11 K17; lia | clear - HV2l HV2r K3l K3r K11 K17; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K18) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K18) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | exactA K25]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K26]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K3l K3r K11 K17; lia | clear - HV2l HV2r K3l K3r K11 K17; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear - HV41l HV41r) | clear - HV2l HV2r K3l K3r K11 K17; lia | clear - HV2l HV2r K3l K3r K11 K17; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV2l HV2r K3l K3r K11 K17; lia | clear - HV2l HV2r K3l K3r K11 K17; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K3l K3r K11 K17; lia | clear - HV2l HV2r K3l K3r K11 K17; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K3l K3r K11 K17; lia | clear - HV2l HV2r K3l K3r K11 K17; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K3l K3r K11 K17; lia | clear - HV2l HV2r K3l K3r K11 K17; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K34l K34r) | exact (conj K34l K34r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PafbB2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PafbB2.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> ~ ((vz_37 + 152) <= bv_unsigned a < (vz_37 + 152) + 4) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PafbB2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K17 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV37l HV37r K12l K12r K14 K17 K18 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PafbB2.ps0) with 0xb2c80 in Hms. change (SR.ps_regs PafbB2.ps0) with (map (fun i => (i, nth i PafbB2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PafbB2.ps0) with PafbB2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PafbB2.regs0 PafbB2.regs_out0 60 KS_afbB2 KS_afbB2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PafbB2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PafbB2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafbB2.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PafbB2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafbB2.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PafbB2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafbB2.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PafbB2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafbB2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PafbB2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafbB2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PafbB2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafbB2.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PafbB2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafbB2.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PafbB2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafbB2.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PafbB2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafbB2.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PafbB2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear - HV41l HV41r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear - HV42l HV42r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

End PMAFBP.
