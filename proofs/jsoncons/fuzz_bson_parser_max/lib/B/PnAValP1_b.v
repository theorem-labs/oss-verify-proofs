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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require LibSegBa_avlE_b LibSegBa_avlHf_b LibSegBa_avlHsZ_b LibSegBa_avlHsP1_b LibSegBa_avlHsP2_b LibSegBa_avlHsP3_b LibSegBa_avlHsP4_b LibSegBa_avlHsP5_b LibSegBa_avlHsP6_b LibSegBa_avlHsP7_b LibSegBa_avlS_b LibSegBa_avlT0_b LibSegBa_avlT1a_b LibSegBa_avlT1b_b LibSegBa_avlT2a_b LibSegBa_avlT2b_b LibSegBa_avlT3a_b LibSegBa_avlT3b_b LibSegBa_avlTbig_b LibSegBa_avlL_b LibSegBa_avlB_b LibSegBa_avlX_b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PMAVALP1.
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
Module PavlE := LibSegBa_avlE_b.
Definition KS_avlE_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavlE.regs0 PavlE.regs_out0).
Lemma KS_avlE_0_ok : BG.kept_ok 60 PavlE.regs0 PavlE.regs_out0 KS_avlE_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlE_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavlE.regs0 PavlE.regs_out1).
Lemma KS_avlE_1_ok : BG.kept_ok 60 PavlE.regs0 PavlE.regs_out1 KS_avlE_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlE_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 35%nat) ->
  L5.img_clear M 1249280 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487264 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> 0 <= (V 33%nat) <= 140737488355328 -> 0 <= (V 35%nat) <= 67108863 -> L5.writable RSEGS M ((V 2%nat) - 112) 112 ->
  1 <= (Z.lxor (if 0 <? (V 33%nat) then 1 else 0) (if (((V 33%nat) + (V 35%nat)) mod 2 ^ 64) <? 1 then 1 else 0)) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 112) <= bv_unsigned a < ((V 2%nat) - 112) + 112) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 112) <= i < ((V 2%nat) - 112) + 112) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb2f54 M) (st fx' R' 0xb3300 M')
        /\ (forall x, In x KS_avlE_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 112)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat))
        /\ bv_unsigned (getr R' (reg 14)) = (if (((V 33%nat) + (V 35%nat)) mod 2 ^ 64) <? 1 then 1 else 0)
        /\ (((V 35%nat) - 0) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (bv_unsigned (getr R (reg 27)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (bv_unsigned (getr R (reg 26)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (bv_unsigned (getr R (reg 25)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))
      \/ (msteps RSEGS (st fx R 0xb2f54 M) (st fx' R' 0xb3004 M')
        /\ (forall x, In x KS_avlE_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 112)
        /\ getr R' (reg 5) = Z_to_bv 64 245
        /\ getr R' (reg 6) = Z_to_bv 64 2
        /\ getr R' (reg 7) = Z_to_bv 64 18446744073709551551
        /\ getr R' (reg 8) = Z_to_bv 64 159
        /\ getr R' (reg 9) = Z_to_bv 64 240
        /\ getr R' (reg 11) = Z_to_bv 64 1309752
        /\ getr R' (reg 12) = Z_to_bv 64 143284
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat))
        /\ getr R' (reg 14) = Z_to_bv 64 8
        /\ getr R' (reg 15) = Z_to_bv 64 18446744073709551615
        /\ getr R' (reg 16) = Z_to_bv 64 1
        /\ getr R' (reg 17) = Z_to_bv 64 18446744073709551554
        /\ getr R' (reg 18) = Z_to_bv 64 145280
        /\ getr R' (reg 19) = Z_to_bv 64 18446744073709406335
        /\ getr R' (reg 20) = Z_to_bv 64 2147450880
        /\ getr R' (reg 21) = Z_to_bv 64 144
        /\ getr R' (reg 22) = Z_to_bv 64 244
        /\ getr R' (reg 23) = Z_to_bv 64 143
        /\ getr R' (reg 24) = Z_to_bv 64 3
        /\ getr R' (reg 28) = Z_to_bv 64 239
        /\ getr R' (reg 29) = Z_to_bv 64 224
        /\ getr R' (reg 30) = Z_to_bv 64 160
        /\ getr R' (reg 31) = Z_to_bv 64 237
        /\ 1 <= (((V 35%nat) - 0) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (bv_unsigned (getr R (reg 27)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (bv_unsigned (getr R (reg 26)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (bv_unsigned (getr R (reg 25)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G10 G11 K0 K1 K2 pvzI4 K4 pvzI5 pvzI6 K7 K8.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K3l; move K3l before pvzI4; pose proof (proj2 pvzI4) as K3r; move K3r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K5l; move K5l before pvzI5; pose proof (proj2 pvzI5) as K5r; move K5r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K6l; move K6l before pvzI6; pose proof (proj2 pvzI6) as K6r; move K6r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 36%nat. }
  assert (HR: regs_ok E PavlE.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlE.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlE.kn0).
  { unfold know_ok, PavlE.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K8]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlE.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlE.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 112) <= bv_unsigned a < (vz_2 - 112) + 112) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PavlE.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavlE.ps0) with 0xb3300 in Hms. change (SR.ps_regs PavlE.ps0) with (map (fun i => (i, nth i PavlE.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlE.ps0) with PavlE.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlE.regs0 PavlE.regs_out0 60 KS_avlE_0 KS_avlE_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlE.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PavlE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlE.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavlE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlE.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PavlE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlE.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PavlE.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
  - right.
    change (SR.ps_pc PavlE.ps1) with 0xb3004 in Hms. change (SR.ps_regs PavlE.ps1) with (map (fun i => (i, nth i PavlE.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlE.ps1) with PavlE.cells1 in Hcells. unfold PavlE.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlE.regs0 PavlE.regs_out1 60 KS_avlE_1 KS_avlE_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlE.regs_out1 E' R' 2 Hregs) by (clear; lia). cbn [nth PavlE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlE.regs_out1 E' R' 5 Hregs) by (clear; lia). cbn [nth PavlE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlE.regs_out1 E' R' 6 Hregs) by (clear; lia). cbn [nth PavlE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlE.regs_out1 E' R' 7 Hregs) by (clear; lia). cbn [nth PavlE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlE.regs_out1 E' R' 8 Hregs) by (clear; lia). cbn [nth PavlE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlE.regs_out1 E' R' 9 Hregs) by (clear; lia). cbn [nth PavlE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlE.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlE.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PavlE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlE.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PavlE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlE.regs_out1 E' R' 14 Hregs) by (clear; lia). cbn [nth PavlE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlE.regs_out1 E' R' 15 Hregs) by (clear; lia). cbn [nth PavlE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlE.regs_out1 E' R' 16 Hregs) by (clear; lia). cbn [nth PavlE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlE.regs_out1 E' R' 17 Hregs) by (clear; lia). cbn [nth PavlE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlE.regs_out1 E' R' 18 Hregs) by (clear; lia). cbn [nth PavlE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlE.regs_out1 E' R' 19 Hregs) by (clear; lia). cbn [nth PavlE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlE.regs_out1 E' R' 20 Hregs) by (clear; lia). cbn [nth PavlE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlE.regs_out1 E' R' 21 Hregs) by (clear; lia). cbn [nth PavlE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlE.regs_out1 E' R' 22 Hregs) by (clear; lia). cbn [nth PavlE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlE.regs_out1 E' R' 23 Hregs) by (clear; lia). cbn [nth PavlE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlE.regs_out1 E' R' 24 Hregs) by (clear; lia). cbn [nth PavlE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlE.regs_out1 E' R' 28 Hregs) by (clear; lia). cbn [nth PavlE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlE.regs_out1 E' R' 29 Hregs) by (clear; lia). cbn [nth PavlE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlE.regs_out1 E' R' 30 Hregs) by (clear; lia). cbn [nth PavlE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlE.regs_out1 E' R' 31 Hregs) by (clear; lia). cbn [nth PavlE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavlHf := LibSegBa_avlHf_b.
Definition KS_avlHf_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavlHf.regs0 PavlHf.regs_out0).
Lemma KS_avlHf_0_ok : BG.kept_ok 60 PavlHf.regs0 PavlHf.regs_out0 KS_avlHf_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlHf_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavlHf.regs0 PavlHf.regs_out1).
Lemma KS_avlHf_1_ok : BG.kept_ok 60 PavlHf.regs0 PavlHf.regs_out1 KS_avlHf_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlHf_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 18446744073709551615 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 145280 -> getr R (reg 19) = Z_to_bv 64 18446744073709406335 -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  1 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M (V 33%nat) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb3004 M) (st fx' R' 0xb312c M')
        /\ (forall x, In x KS_avlHf_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 0)
      \/ (msteps RSEGS (st fx R 0xb3004 M) (st fx' R' 0xb302c M')
        /\ (forall x, In x KS_avlHf_1 -> getr R' (reg x) = getr R (reg x)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavlHf.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlHf.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlHf.kn0).
  { unfold know_ok, PavlHf.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlHf.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlHf.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavlHf.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavlHf.ps0) with 0xb312c in Hms. change (SR.ps_regs PavlHf.ps0) with (map (fun i => (i, nth i PavlHf.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlHf.ps0) with PavlHf.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlHf.regs0 PavlHf.regs_out0 60 KS_avlHf_0 KS_avlHf_0_ok HR Hag Hregs j Hj). }
    rewrite (BG.out_reg PavlHf.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlHf.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
  - right.
    change (SR.ps_pc PavlHf.ps1) with 0xb302c in Hms. change (SR.ps_regs PavlHf.ps1) with (map (fun i => (i, nth i PavlHf.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlHf.ps1) with PavlHf.cells1 in Hcells. unfold PavlHf.cells1 in Hcells.
    split. { exact Hms. }
    intros j Hj. apply (BG.kept_regs E E' R R' PavlHf.regs0 PavlHf.regs_out1 60 KS_avlHf_1 KS_avlHf_1_ok HR Hag Hregs j Hj). 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavlHsZ := LibSegBa_avlHsZ_b.
Definition KS_avlHsZ : list nat := Eval vm_compute in (BG.kept_list 60 PavlHsZ.regs0 PavlHsZ.regs_out0).
Lemma KS_avlHsZ_ok : BG.kept_ok 60 PavlHsZ.regs0 PavlHsZ.regs_out0 KS_avlHsZ = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlHsZ_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  1 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 7 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M (V 33%nat) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3004 M) (st fx' R' 0xb312c M')
        /\ (forall x, In x KS_avlHsZ -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G16 G17 G20 G21 G22 G23 G24 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavlHsZ.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlHsZ.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlHsZ.kn0).
  { unfold know_ok, PavlHsZ.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlHsZ.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlHsZ.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavlHsZ.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PavlHsZ.ps0) with 0xb312c in Hms. change (SR.ps_regs PavlHsZ.ps0) with (map (fun i => (i, nth i PavlHsZ.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PavlHsZ.ps0) with PavlHsZ.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlHsZ.regs0 PavlHsZ.regs_out0 60 KS_avlHsZ KS_avlHsZ_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg PavlHsZ.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlHsZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavlHsP1 := LibSegBa_avlHsP1_b.
Definition KS_avlHsP1 : list nat := Eval vm_compute in (BG.kept_list 60 PavlHsP1.regs0 PavlHsP1.regs_out0).
Lemma KS_avlHsP1_ok : BG.kept_ok 60 PavlHsP1.regs0 PavlHsP1.regs_out0 KS_avlHsP1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlHsP1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  1 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 7 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M (V 33%nat) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M (((V 33%nat) / 8) + 2147450880) 1 -> 0 <= Z.land (V 33%nat) 7 <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3004 M) (st fx' R' 0xb312c M')
        /\ (forall x, In x KS_avlHsP1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G16 G17 G20 G21 G22 G23 G24 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 pvzI9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavlHsP1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlHsP1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlHsP1.kn0).
  { unfold know_ok, PavlHsP1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | clear; lia | exact (conj K6l K6r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlHsP1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlHsP1.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavlHsP1.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PavlHsP1.ps0) with 0xb312c in Hms. change (SR.ps_regs PavlHsP1.ps0) with (map (fun i => (i, nth i PavlHsP1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PavlHsP1.ps0) with PavlHsP1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlHsP1.regs0 PavlHsP1.regs_out0 60 KS_avlHsP1 KS_avlHsP1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PavlHsP1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlHsP1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PavlHsP1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavlHsP1.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavlHsP2 := LibSegBa_avlHsP2_b.
Definition KS_avlHsP2 : list nat := Eval vm_compute in (BG.kept_list 60 PavlHsP2.regs0 PavlHsP2.regs_out0).
Lemma KS_avlHsP2_ok : BG.kept_ok 60 PavlHsP2.regs0 PavlHsP2.regs_out0 KS_avlHsP2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlHsP2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  1 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 7 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M (V 33%nat) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M (((V 33%nat) / 8) + 2147450880) 2 -> 0 <= Z.land (V 33%nat) 7 <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3004 M) (st fx' R' 0xb312c M')
        /\ (forall x, In x KS_avlHsP2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ bv_unsigned (getr R' (reg 12)) = (Z.land (V 33%nat) 7)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G16 G17 G20 G21 G22 G23 G24 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 pvzI9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavlHsP2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlHsP2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlHsP2.kn0).
  { unfold know_ok, PavlHsP2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | clear; lia | exact (conj K6l K6r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlHsP2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlHsP2.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavlHsP2.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PavlHsP2.ps0) with 0xb312c in Hms. change (SR.ps_regs PavlHsP2.ps0) with (map (fun i => (i, nth i PavlHsP2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PavlHsP2.ps0) with PavlHsP2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlHsP2.regs0 PavlHsP2.regs_out0 60 KS_avlHsP2 KS_avlHsP2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PavlHsP2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlHsP2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PavlHsP2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavlHsP2.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavlHsP3 := LibSegBa_avlHsP3_b.
Definition KS_avlHsP3 : list nat := Eval vm_compute in (BG.kept_list 60 PavlHsP3.regs0 PavlHsP3.regs_out0).
Lemma KS_avlHsP3_ok : BG.kept_ok 60 PavlHsP3.regs0 PavlHsP3.regs_out0 KS_avlHsP3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlHsP3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  1 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 7 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M (V 33%nat) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M (((V 33%nat) / 8) + 2147450880) 3 -> 0 <= Z.land (V 33%nat) 7 <= 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3004 M) (st fx' R' 0xb312c M')
        /\ (forall x, In x KS_avlHsP3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 3
        /\ bv_unsigned (getr R' (reg 12)) = (Z.land (V 33%nat) 7)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G16 G17 G20 G21 G22 G23 G24 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 pvzI9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavlHsP3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlHsP3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlHsP3.kn0).
  { unfold know_ok, PavlHsP3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | clear; lia | exact (conj K6l K6r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlHsP3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlHsP3.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavlHsP3.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PavlHsP3.ps0) with 0xb312c in Hms. change (SR.ps_regs PavlHsP3.ps0) with (map (fun i => (i, nth i PavlHsP3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PavlHsP3.ps0) with PavlHsP3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlHsP3.regs0 PavlHsP3.regs_out0 60 KS_avlHsP3 KS_avlHsP3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PavlHsP3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlHsP3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PavlHsP3.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavlHsP3.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavlHsP4 := LibSegBa_avlHsP4_b.
Definition KS_avlHsP4 : list nat := Eval vm_compute in (BG.kept_list 60 PavlHsP4.regs0 PavlHsP4.regs_out0).
Lemma KS_avlHsP4_ok : BG.kept_ok 60 PavlHsP4.regs0 PavlHsP4.regs_out0 KS_avlHsP4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlHsP4_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  1 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 7 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M (V 33%nat) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M (((V 33%nat) / 8) + 2147450880) 4 -> 0 <= Z.land (V 33%nat) 7 <= 3 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3004 M) (st fx' R' 0xb312c M')
        /\ (forall x, In x KS_avlHsP4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 4
        /\ bv_unsigned (getr R' (reg 12)) = (Z.land (V 33%nat) 7)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G16 G17 G20 G21 G22 G23 G24 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 pvzI9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavlHsP4.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlHsP4.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlHsP4.kn0).
  { unfold know_ok, PavlHsP4.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | clear; lia | exact (conj K6l K6r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlHsP4.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlHsP4.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavlHsP4.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PavlHsP4.ps0) with 0xb312c in Hms. change (SR.ps_regs PavlHsP4.ps0) with (map (fun i => (i, nth i PavlHsP4.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PavlHsP4.ps0) with PavlHsP4.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlHsP4.regs0 PavlHsP4.regs_out0 60 KS_avlHsP4 KS_avlHsP4_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PavlHsP4.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlHsP4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PavlHsP4.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavlHsP4.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavlHsP5 := LibSegBa_avlHsP5_b.
Definition KS_avlHsP5 : list nat := Eval vm_compute in (BG.kept_list 60 PavlHsP5.regs0 PavlHsP5.regs_out0).
Lemma KS_avlHsP5_ok : BG.kept_ok 60 PavlHsP5.regs0 PavlHsP5.regs_out0 KS_avlHsP5 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlHsP5_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  1 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 7 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M (V 33%nat) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M (((V 33%nat) / 8) + 2147450880) 5 -> 0 <= Z.land (V 33%nat) 7 <= 4 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3004 M) (st fx' R' 0xb312c M')
        /\ (forall x, In x KS_avlHsP5 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 5
        /\ bv_unsigned (getr R' (reg 12)) = (Z.land (V 33%nat) 7)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G16 G17 G20 G21 G22 G23 G24 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 pvzI9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavlHsP5.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlHsP5.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlHsP5.kn0).
  { unfold know_ok, PavlHsP5.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | clear; lia | exact (conj K6l K6r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlHsP5.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlHsP5.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavlHsP5.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PavlHsP5.ps0) with 0xb312c in Hms. change (SR.ps_regs PavlHsP5.ps0) with (map (fun i => (i, nth i PavlHsP5.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PavlHsP5.ps0) with PavlHsP5.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlHsP5.regs0 PavlHsP5.regs_out0 60 KS_avlHsP5 KS_avlHsP5_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PavlHsP5.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlHsP5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PavlHsP5.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavlHsP5.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavlHsP6 := LibSegBa_avlHsP6_b.
Definition KS_avlHsP6 : list nat := Eval vm_compute in (BG.kept_list 60 PavlHsP6.regs0 PavlHsP6.regs_out0).
Lemma KS_avlHsP6_ok : BG.kept_ok 60 PavlHsP6.regs0 PavlHsP6.regs_out0 KS_avlHsP6 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlHsP6_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  1 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 7 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M (V 33%nat) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M (((V 33%nat) / 8) + 2147450880) 6 -> 0 <= Z.land (V 33%nat) 7 <= 5 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3004 M) (st fx' R' 0xb312c M')
        /\ (forall x, In x KS_avlHsP6 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ bv_unsigned (getr R' (reg 12)) = (Z.land (V 33%nat) 7)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G16 G17 G20 G21 G22 G23 G24 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 pvzI9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavlHsP6.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlHsP6.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlHsP6.kn0).
  { unfold know_ok, PavlHsP6.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | clear; lia | exact (conj K6l K6r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlHsP6.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlHsP6.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavlHsP6.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PavlHsP6.ps0) with 0xb312c in Hms. change (SR.ps_regs PavlHsP6.ps0) with (map (fun i => (i, nth i PavlHsP6.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PavlHsP6.ps0) with PavlHsP6.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlHsP6.regs0 PavlHsP6.regs_out0 60 KS_avlHsP6 KS_avlHsP6_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PavlHsP6.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlHsP6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PavlHsP6.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavlHsP6.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavlHsP7 := LibSegBa_avlHsP7_b.
Definition KS_avlHsP7 : list nat := Eval vm_compute in (BG.kept_list 60 PavlHsP7.regs0 PavlHsP7.regs_out0).
Lemma KS_avlHsP7_ok : BG.kept_ok 60 PavlHsP7.regs0 PavlHsP7.regs_out0 KS_avlHsP7 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlHsP7_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  1 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 7 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M (V 33%nat) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M (((V 33%nat) / 8) + 2147450880) 7 -> 0 <= Z.land (V 33%nat) 7 <= 6 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3004 M) (st fx' R' 0xb312c M')
        /\ (forall x, In x KS_avlHsP7 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 7
        /\ bv_unsigned (getr R' (reg 12)) = (Z.land (V 33%nat) 7)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G16 G17 G20 G21 G22 G23 G24 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 pvzI9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavlHsP7.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlHsP7.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlHsP7.kn0).
  { unfold know_ok, PavlHsP7.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | clear; lia | exact (conj K6l K6r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlHsP7.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlHsP7.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavlHsP7.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PavlHsP7.ps0) with 0xb312c in Hms. change (SR.ps_regs PavlHsP7.ps0) with (map (fun i => (i, nth i PavlHsP7.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PavlHsP7.ps0) with PavlHsP7.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlHsP7.regs0 PavlHsP7.regs_out0 60 KS_avlHsP7 KS_avlHsP7_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PavlHsP7.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlHsP7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PavlHsP7.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavlHsP7.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavlS := LibSegBa_avlS_b.
Definition KS_avlS : list nat := Eval vm_compute in (BG.kept_list 60 PavlS.regs0 PavlS.regs_out0).
Lemma KS_avlS_ok : BG.kept_ok 60 PavlS.regs0 PavlS.regs_out0 KS_avlS = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 18446744073709551615 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 145280 -> getr R (reg 19) = Z_to_bv 64 18446744073709406335 -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  0 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M (V 33%nat) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5KA.zeros_at M 2147469040 32 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb312c M) (st fx' R' 0xb3148 M')
        /\ (forall x, In x KS_avlS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 36%nat) + 145280)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 25) = Z_to_bv 64 (V 36%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavlS.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlS.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlS.kn0).
  { unfold know_ok, PavlS.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlS.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlS.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavlS.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PavlS.ps0) with 0xb3148 in Hms. change (SR.ps_regs PavlS.ps0) with (map (fun i => (i, nth i PavlS.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PavlS.ps0) with PavlS.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlS.regs0 PavlS.regs_out0 60 KS_avlS KS_avlS_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PavlS.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavlS.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavlS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PavlS.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PavlS.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavlT0 := LibSegBa_avlT0_b.
Definition KS_avlT0_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavlT0.regs0 PavlT0.regs_out0).
Lemma KS_avlT0_0_ok : BG.kept_ok 60 PavlT0.regs0 PavlT0.regs_out0 KS_avlT0_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlT0_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavlT0.regs0 PavlT0.regs_out1).
Lemma KS_avlT0_1_ok : BG.kept_ok 60 PavlT0.regs0 PavlT0.regs_out1 KS_avlT0_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlT0_2 : list nat := Eval vm_compute in (BG.kept_list 60 PavlT0.regs0 PavlT0.regs_out2).
Lemma KS_avlT0_2_ok : BG.kept_ok 60 PavlT0.regs0 PavlT0.regs_out2 KS_avlT0_2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlT0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 18446744073709551615 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 145280 -> getr R (reg 19) = Z_to_bv 64 18446744073709406335 -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 25) = Z_to_bv 64 (V 37%nat) -> getr R (reg 27) = Z_to_bv 64 0 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  0 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb314c M) (st fx' R' 0xb3300 M')
        /\ (forall x, In x KS_avlT0_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 1))
      \/ (msteps RSEGS (st fx R 0xb314c M) (st fx' R' 0xb3234 M')
        /\ (forall x, In x KS_avlT0_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ (V 37%nat) < 245)
      \/ (msteps RSEGS (st fx R 0xb314c M) (st fx' R' 0xb3300 M')
        /\ (forall x, In x KS_avlT0_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ 245 <= (V 37%nat))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G25 G27 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 pvzI8.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PavlT0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlT0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlT0.kn0).
  { unfold know_ok, PavlT0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlT0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlT0.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavlT0.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PavlT0.ps0) with 0xb3300 in Hms. change (SR.ps_regs PavlT0.ps0) with (map (fun i => (i, nth i PavlT0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlT0.ps0) with PavlT0.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlT0.regs0 PavlT0.regs_out0 60 KS_avlT0_0 KS_avlT0_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlT0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlT0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PavlT0.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PavlT0.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. left.
    change (SR.ps_pc PavlT0.ps1) with 0xb3234 in Hms. change (SR.ps_regs PavlT0.ps1) with (map (fun i => (i, nth i PavlT0.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlT0.ps1) with PavlT0.cells1 in Hcells. unfold PavlT0.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlT0.regs0 PavlT0.regs_out1 60 KS_avlT0_1 KS_avlT0_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlT0.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlT0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlT0.regs_out1 E' R' 26 Hregs) by (clear; lia). cbn [nth PavlT0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. 
    change (SR.ps_pc PavlT0.ps2) with 0xb3300 in Hms. change (SR.ps_regs PavlT0.ps2) with (map (fun i => (i, nth i PavlT0.regs_out2 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlT0.ps2) with PavlT0.cells2 in Hcells. unfold PavlT0.cells2 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlT0.regs0 PavlT0.regs_out2 60 KS_avlT0_2 KS_avlT0_2_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlT0.regs_out2 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlT0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlT0.regs_out2 E' R' 26 Hregs) by (clear; lia). cbn [nth PavlT0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavlT1a := LibSegBa_avlT1a_b.
Definition KS_avlT1a : list nat := Eval vm_compute in (BG.kept_list 60 PavlT1a.regs0 PavlT1a.regs_out0).
Lemma KS_avlT1a_ok : BG.kept_ok 60 PavlT1a.regs0 PavlT1a.regs_out0 KS_avlT1a = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlT1a_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 18446744073709551615 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 145280 -> getr R (reg 19) = Z_to_bv 64 18446744073709406335 -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 25) = Z_to_bv 64 (V 37%nat) -> getr R (reg 27) = Z_to_bv 64 1 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  0 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 1 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb314c M) (st fx' R' 0xb3300 M')
        /\ (forall x, In x KS_avlT1a -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 5).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G25 G27 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 pvzI8.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PavlT1a.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlT1a.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlT1a.kn0).
  { unfold know_ok, PavlT1a.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlT1a.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlT1a.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavlT1a.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PavlT1a.ps0) with 0xb3300 in Hms. change (SR.ps_regs PavlT1a.ps0) with (map (fun i => (i, nth i PavlT1a.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PavlT1a.ps0) with PavlT1a.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlT1a.regs0 PavlT1a.regs_out0 60 KS_avlT1a KS_avlT1a_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg PavlT1a.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlT1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavlT1b := LibSegBa_avlT1b_b.
Definition KS_avlT1b : list nat := Eval vm_compute in (BG.kept_list 60 PavlT1b.regs0 PavlT1b.regs_out0).
Lemma KS_avlT1b_ok : BG.kept_ok 60 PavlT1b.regs0 PavlT1b.regs_out0 KS_avlT1b = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlT1b_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 18446744073709551615 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 145280 -> getr R (reg 19) = Z_to_bv 64 18446744073709406335 -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 25) = Z_to_bv 64 (V 37%nat) -> getr R (reg 27) = Z_to_bv 64 1 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  0 <= (V 33%nat) <= 140737488355328 -> 2 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb314c M) (st fx' R' 0xb31cc M')
        /\ (forall x, In x KS_avlT1b -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 2)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G25 G27 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 pvzI8.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PavlT1b.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlT1b.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlT1b.kn0).
  { unfold know_ok, PavlT1b.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlT1b.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlT1b.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavlT1b.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PavlT1b.ps0) with 0xb31cc in Hms. change (SR.ps_regs PavlT1b.ps0) with (map (fun i => (i, nth i PavlT1b.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PavlT1b.ps0) with PavlT1b.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlT1b.regs0 PavlT1b.regs_out0 60 KS_avlT1b KS_avlT1b_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PavlT1b.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlT1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavlT1b.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavlT1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PavlT1b.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PavlT1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavlT2a := LibSegBa_avlT2a_b.
Definition KS_avlT2a : list nat := Eval vm_compute in (BG.kept_list 60 PavlT2a.regs0 PavlT2a.regs_out0).
Lemma KS_avlT2a_ok : BG.kept_ok 60 PavlT2a.regs0 PavlT2a.regs_out0 KS_avlT2a = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlT2a_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 18446744073709551615 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 145280 -> getr R (reg 19) = Z_to_bv 64 18446744073709406335 -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 25) = Z_to_bv 64 (V 37%nat) -> getr R (reg 27) = Z_to_bv 64 2 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  0 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 2 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb314c M) (st fx' R' 0xb3300 M')
        /\ (forall x, In x KS_avlT2a -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 5).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G25 G27 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 pvzI8.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PavlT2a.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlT2a.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlT2a.kn0).
  { unfold know_ok, PavlT2a.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlT2a.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlT2a.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavlT2a.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PavlT2a.ps0) with 0xb3300 in Hms. change (SR.ps_regs PavlT2a.ps0) with (map (fun i => (i, nth i PavlT2a.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PavlT2a.ps0) with PavlT2a.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlT2a.regs0 PavlT2a.regs_out0 60 KS_avlT2a KS_avlT2a_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg PavlT2a.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlT2a.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavlT2b := LibSegBa_avlT2b_b.
Definition KS_avlT2b : list nat := Eval vm_compute in (BG.kept_list 60 PavlT2b.regs0 PavlT2b.regs_out0).
Lemma KS_avlT2b_ok : BG.kept_ok 60 PavlT2b.regs0 PavlT2b.regs_out0 KS_avlT2b = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlT2b_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 18446744073709551615 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 145280 -> getr R (reg 19) = Z_to_bv 64 18446744073709406335 -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 25) = Z_to_bv 64 (V 37%nat) -> getr R (reg 27) = Z_to_bv 64 2 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  0 <= (V 33%nat) <= 140737488355328 -> 3 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb314c M) (st fx' R' 0xb31ac M')
        /\ (forall x, In x KS_avlT2b -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 3)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G25 G27 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 pvzI8.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PavlT2b.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlT2b.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlT2b.kn0).
  { unfold know_ok, PavlT2b.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlT2b.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlT2b.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavlT2b.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PavlT2b.ps0) with 0xb31ac in Hms. change (SR.ps_regs PavlT2b.ps0) with (map (fun i => (i, nth i PavlT2b.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PavlT2b.ps0) with PavlT2b.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlT2b.regs0 PavlT2b.regs_out0 60 KS_avlT2b KS_avlT2b_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PavlT2b.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PavlT2b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavlT2b.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlT2b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavlT2b.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavlT2b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PavlT2b.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PavlT2b.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavlT3a := LibSegBa_avlT3a_b.
Definition KS_avlT3a : list nat := Eval vm_compute in (BG.kept_list 60 PavlT3a.regs0 PavlT3a.regs_out0).
Lemma KS_avlT3a_ok : BG.kept_ok 60 PavlT3a.regs0 PavlT3a.regs_out0 KS_avlT3a = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlT3a_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 18446744073709551615 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 145280 -> getr R (reg 19) = Z_to_bv 64 18446744073709406335 -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 25) = Z_to_bv 64 (V 37%nat) -> getr R (reg 27) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  0 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 3 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb314c M) (st fx' R' 0xb3300 M')
        /\ (forall x, In x KS_avlT3a -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 5).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G25 G27 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 pvzI8.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PavlT3a.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlT3a.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlT3a.kn0).
  { unfold know_ok, PavlT3a.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlT3a.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlT3a.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavlT3a.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PavlT3a.ps0) with 0xb3300 in Hms. change (SR.ps_regs PavlT3a.ps0) with (map (fun i => (i, nth i PavlT3a.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PavlT3a.ps0) with PavlT3a.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlT3a.regs0 PavlT3a.regs_out0 60 KS_avlT3a KS_avlT3a_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg PavlT3a.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlT3a.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavlT3b := LibSegBa_avlT3b_b.
Definition KS_avlT3b : list nat := Eval vm_compute in (BG.kept_list 60 PavlT3b.regs0 PavlT3b.regs_out0).
Lemma KS_avlT3b_ok : BG.kept_ok 60 PavlT3b.regs0 PavlT3b.regs_out0 KS_avlT3b = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlT3b_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 18446744073709551615 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 145280 -> getr R (reg 19) = Z_to_bv 64 18446744073709406335 -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 25) = Z_to_bv 64 (V 37%nat) -> getr R (reg 27) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  0 <= (V 33%nat) <= 140737488355328 -> 4 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb314c M) (st fx' R' 0xb318c M')
        /\ (forall x, In x KS_avlT3b -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 ((V 33%nat) + 4)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 4)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G25 G27 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 pvzI8.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PavlT3b.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlT3b.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlT3b.kn0).
  { unfold know_ok, PavlT3b.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlT3b.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlT3b.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavlT3b.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PavlT3b.ps0) with 0xb318c in Hms. change (SR.ps_regs PavlT3b.ps0) with (map (fun i => (i, nth i PavlT3b.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PavlT3b.ps0) with PavlT3b.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlT3b.regs0 PavlT3b.regs_out0 60 KS_avlT3b KS_avlT3b_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PavlT3b.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PavlT3b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavlT3b.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlT3b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavlT3b.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavlT3b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PavlT3b.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PavlT3b.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavlTbig := LibSegBa_avlTbig_b.
Definition KS_avlTbig_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavlTbig.regs0 PavlTbig.regs_out0).
Lemma KS_avlTbig_0_ok : BG.kept_ok 60 PavlTbig.regs0 PavlTbig.regs_out0 KS_avlTbig_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlTbig_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavlTbig.regs0 PavlTbig.regs_out1).
Lemma KS_avlTbig_1_ok : BG.kept_ok 60 PavlTbig.regs0 PavlTbig.regs_out1 KS_avlTbig_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlTbig_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 18446744073709551615 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 145280 -> getr R (reg 19) = Z_to_bv 64 18446744073709406335 -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 25) = Z_to_bv 64 (V 37%nat) -> getr R (reg 27) = Z_to_bv 64 (V 38%nat) -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  0 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  4 <= (V 38%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb314c M) (st fx' R' 0xb3300 M')
        /\ (forall x, In x KS_avlTbig_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (((V 33%nat) + (V 38%nat)) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + (V 38%nat))
        /\ getr R' (reg 26) = Z_to_bv 64 (((V 33%nat) + (V 38%nat)) + 1)
        /\ (V 38%nat) < (V 35%nat))
      \/ (msteps RSEGS (st fx R 0xb314c M) (st fx' R' 0xb3300 M')
        /\ (forall x, In x KS_avlTbig_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 5
        /\ (V 35%nat) <= (V 38%nat))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G5 G6 G7 G8 G9 G10 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G25 G27 G28 G29 G30 G31 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K1l; move K1l before pvzI7; pose proof (proj2 pvzI7) as K1r; move K1r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K2l; move K2l before pvzI8; pose proof (proj2 pvzI8) as K2r; move K2r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K4l; move K4l before pvzI10; pose proof (proj2 pvzI10) as K4r; move K4r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 37%nat => vz_37 | 38%nat => vz_38 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 39%nat. }
  assert (HR: regs_ok E PavlTbig.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlTbig.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlTbig.kn0).
  { unfold know_ok, PavlTbig.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlTbig.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlTbig.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavlTbig.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavlTbig.ps0) with 0xb3300 in Hms. change (SR.ps_regs PavlTbig.ps0) with (map (fun i => (i, nth i PavlTbig.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlTbig.ps0) with PavlTbig.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlTbig.regs0 PavlTbig.regs_out0 60 KS_avlTbig_0 KS_avlTbig_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlTbig.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PavlTbig.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlTbig.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlTbig.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlTbig.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavlTbig.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlTbig.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PavlTbig.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  - right.
    change (SR.ps_pc PavlTbig.ps1) with 0xb3300 in Hms. change (SR.ps_regs PavlTbig.ps1) with (map (fun i => (i, nth i PavlTbig.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlTbig.ps1) with PavlTbig.cells1 in Hcells. unfold PavlTbig.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlTbig.regs0 PavlTbig.regs_out1 60 KS_avlTbig_1 KS_avlTbig_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlTbig.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlTbig.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavlL := LibSegBa_avlL_b.
Definition KS_avlL_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavlL.regs0 PavlL.regs_out0).
Lemma KS_avlL_0_ok : BG.kept_ok 60 PavlL.regs0 PavlL.regs_out0 KS_avlL_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlL_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavlL.regs0 PavlL.regs_out1).
Lemma KS_avlL_1_ok : BG.kept_ok 60 PavlL.regs0 PavlL.regs_out1 KS_avlL_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlL_2 : list nat := Eval vm_compute in (BG.kept_list 60 PavlL.regs0 PavlL.regs_out2).
Lemma KS_avlL_2_ok : BG.kept_ok 60 PavlL.regs0 PavlL.regs_out2 KS_avlL_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlL_3 : list nat := Eval vm_compute in (BG.kept_list 60 PavlL.regs0 PavlL.regs_out3).
Lemma KS_avlL_3_ok : BG.kept_ok 60 PavlL.regs0 PavlL.regs_out3 KS_avlL_3 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlL_4 : list nat := Eval vm_compute in (BG.kept_list 60 PavlL.regs0 PavlL.regs_out4).
Lemma KS_avlL_4_ok : BG.kept_ok 60 PavlL.regs0 PavlL.regs_out4 KS_avlL_4 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlL_5 : list nat := Eval vm_compute in (BG.kept_list 60 PavlL.regs0 PavlL.regs_out5).
Lemma KS_avlL_5_ok : BG.kept_ok 60 PavlL.regs0 PavlL.regs_out5 KS_avlL_5 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlL_6 : list nat := Eval vm_compute in (BG.kept_list 60 PavlL.regs0 PavlL.regs_out6).
Lemma KS_avlL_6_ok : BG.kept_ok 60 PavlL.regs0 PavlL.regs_out6 KS_avlL_6 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlL_7 : list nat := Eval vm_compute in (BG.kept_list 60 PavlL.regs0 PavlL.regs_out7).
Lemma KS_avlL_7_ok : BG.kept_ok 60 PavlL.regs0 PavlL.regs_out7 KS_avlL_7 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlL_8 : list nat := Eval vm_compute in (BG.kept_list 60 PavlL.regs0 PavlL.regs_out8).
Lemma KS_avlL_8_ok : BG.kept_ok 60 PavlL.regs0 PavlL.regs_out8 KS_avlL_8 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlL_9 : list nat := Eval vm_compute in (BG.kept_list 60 PavlL.regs0 PavlL.regs_out9).
Lemma KS_avlL_9_ok : BG.kept_ok 60 PavlL.regs0 PavlL.regs_out9 KS_avlL_9 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlL_10 : list nat := Eval vm_compute in (BG.kept_list 60 PavlL.regs0 PavlL.regs_out10).
Lemma KS_avlL_10_ok : BG.kept_ok 60 PavlL.regs0 PavlL.regs_out10 KS_avlL_10 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlL_11 : list nat := Eval vm_compute in (BG.kept_list 60 PavlL.regs0 PavlL.regs_out11).
Lemma KS_avlL_11_ok : BG.kept_ok 60 PavlL.regs0 PavlL.regs_out11 KS_avlL_11 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlL_12 : list nat := Eval vm_compute in (BG.kept_list 60 PavlL.regs0 PavlL.regs_out12).
Lemma KS_avlL_12_ok : BG.kept_ok 60 PavlL.regs0 PavlL.regs_out12 KS_avlL_12 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlL_13 : list nat := Eval vm_compute in (BG.kept_list 60 PavlL.regs0 PavlL.regs_out13).
Lemma KS_avlL_13_ok : BG.kept_ok 60 PavlL.regs0 PavlL.regs_out13 KS_avlL_13 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 39%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 18446744073709551615 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 145280 -> getr R (reg 19) = Z_to_bv 64 18446744073709406335 -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 25) = Z_to_bv 64 (V 37%nat) -> getr R (reg 26) = Z_to_bv 64 (V 34%nat) -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  0 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  0 <= (V 34%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb31e8 M) (st fx' R' 0xb3300 M')
        /\ (forall x, In x KS_avlL_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ (Z.land (V 39%nat) 255) < 144
        /\ (((V 37%nat) - 240) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0xb31e8 M) (st fx' R' 0xb3234 M')
        /\ (forall x, In x KS_avlL_1 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 11)) = (Z.land (V 39%nat) 255)
        /\ 144 <= (Z.land (V 39%nat) 255)
        /\ (((V 37%nat) - 240) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0xb31e8 M) (st fx' R' 0xb3300 M')
        /\ (forall x, In x KS_avlL_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ 143 < (Z.land (V 39%nat) 255)
        /\ (((V 37%nat) - 244) mod 2 ^ 64) < 1
        /\ 1 <= (((V 37%nat) - 240) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xb31e8 M) (st fx' R' 0xb3234 M')
        /\ (forall x, In x KS_avlL_3 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 11)) = (Z.land (V 39%nat) 255)
        /\ (Z.land (V 39%nat) 255) <= 143
        /\ (((V 37%nat) - 244) mod 2 ^ 64) < 1
        /\ 1 <= (((V 37%nat) - 240) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xb31e8 M) (st fx' R' 0xb3300 M')
        /\ (forall x, In x KS_avlL_4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ 1 <= (((V 37%nat) - 244) mod 2 ^ 64)
        /\ 1 <= (((V 37%nat) - 240) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xb31e8 M) (st fx' R' 0xb3234 M')
        /\ (forall x, In x KS_avlL_5 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ (V 37%nat) < 245
        /\ 1 <= (((V 37%nat) - 244) mod 2 ^ 64)
        /\ 1 <= (((V 37%nat) - 240) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xb31e8 M) (st fx' R' 0xb3300 M')
        /\ (forall x, In x KS_avlL_6 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ 245 <= (V 37%nat)
        /\ 1 <= (((V 37%nat) - 244) mod 2 ^ 64)
        /\ 1 <= (((V 37%nat) - 240) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xb31e8 M) (st fx' R' 0xb3300 M')
        /\ (forall x, In x KS_avlL_7 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ (Z.land (V 39%nat) 255) < 160
        /\ (((V 37%nat) - 224) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0xb31e8 M) (st fx' R' 0xb3234 M')
        /\ (forall x, In x KS_avlL_8 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 11)) = (Z.land (V 39%nat) 255)
        /\ 160 <= (Z.land (V 39%nat) 255)
        /\ (((V 37%nat) - 224) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0xb31e8 M) (st fx' R' 0xb3300 M')
        /\ (forall x, In x KS_avlL_9 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ 159 < (Z.land (V 39%nat) 255)
        /\ (((V 37%nat) - 237) mod 2 ^ 64) < 1
        /\ 1 <= (((V 37%nat) - 224) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xb31e8 M) (st fx' R' 0xb3234 M')
        /\ (forall x, In x KS_avlL_10 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 11)) = (Z.land (V 39%nat) 255)
        /\ (Z.land (V 39%nat) 255) <= 159
        /\ (((V 37%nat) - 237) mod 2 ^ 64) < 1
        /\ 1 <= (((V 37%nat) - 224) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xb31e8 M) (st fx' R' 0xb3300 M')
        /\ (forall x, In x KS_avlL_11 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ 1 <= (((V 37%nat) - 237) mod 2 ^ 64)
        /\ 1 <= (((V 37%nat) - 224) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xb31e8 M) (st fx' R' 0xb3234 M')
        /\ (forall x, In x KS_avlL_12 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ (V 37%nat) < 245
        /\ 1 <= (((V 37%nat) - 237) mod 2 ^ 64)
        /\ 1 <= (((V 37%nat) - 224) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xb31e8 M) (st fx' R' 0xb3300 M')
        /\ (forall x, In x KS_avlL_13 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ 245 <= (V 37%nat)
        /\ 1 <= (((V 37%nat) - 237) mod 2 ^ 64)
        /\ 1 <= (((V 37%nat) - 224) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G5 G6 G7 G8 G9 G10 G11 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G25 G26 G28 G29 G30 G31 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV39l; move HV39l before pvzI6; pose proof (proj2 pvzI6) as HV39r; move HV39r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K1l; move K1l before pvzI8; pose proof (proj2 pvzI8) as K1r; move K1r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K2l; move K2l before pvzI9; pose proof (proj2 pvzI9) as K2r; move K2r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K4l; move K4l before pvzI11; pose proof (proj2 pvzI11) as K4r; move K4r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_39 := V 39%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | 39%nat => Z_to_bv 64 vz_39 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 37%nat => vz_37 | 39%nat => vz_39 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 40%nat. }
  assert (HR: regs_ok E PavlL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlL.kn0).
  { unfold know_ok, PavlL.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlL.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavlL.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PavlL.ps0) with 0xb3300 in Hms. change (SR.ps_regs PavlL.ps0) with (map (fun i => (i, nth i PavlL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlL.ps0) with PavlL.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlL.regs0 PavlL.regs_out0 60 KS_avlL_0 KS_avlL_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlL.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. left.
    change (SR.ps_pc PavlL.ps1) with 0xb3234 in Hms. change (SR.ps_regs PavlL.ps1) with (map (fun i => (i, nth i PavlL.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlL.ps1) with PavlL.cells1 in Hcells. unfold PavlL.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlL.regs0 PavlL.regs_out1 60 KS_avlL_1 KS_avlL_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlL.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlL.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. left.
    change (SR.ps_pc PavlL.ps2) with 0xb3300 in Hms. change (SR.ps_regs PavlL.ps2) with (map (fun i => (i, nth i PavlL.regs_out2 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlL.ps2) with PavlL.cells2 in Hcells. unfold PavlL.cells2 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlL.regs0 PavlL.regs_out2 60 KS_avlL_2 KS_avlL_2_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlL.regs_out2 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlL.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. left.
    change (SR.ps_pc PavlL.ps3) with 0xb3234 in Hms. change (SR.ps_regs PavlL.ps3) with (map (fun i => (i, nth i PavlL.regs_out3 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlL.ps3) with PavlL.cells3 in Hcells. unfold PavlL.cells3 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlL.regs0 PavlL.regs_out3 60 KS_avlL_3 KS_avlL_3_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlL.regs_out3 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlL.regs_out3]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. left.
    change (SR.ps_pc PavlL.ps4) with 0xb3300 in Hms. change (SR.ps_regs PavlL.ps4) with (map (fun i => (i, nth i PavlL.regs_out4 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlL.ps4) with PavlL.cells4 in Hcells. unfold PavlL.cells4 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlL.regs0 PavlL.regs_out4 60 KS_avlL_4 KS_avlL_4_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlL.regs_out4 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlL.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. left.
    change (SR.ps_pc PavlL.ps5) with 0xb3234 in Hms. change (SR.ps_regs PavlL.ps5) with (map (fun i => (i, nth i PavlL.regs_out5 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlL.ps5) with PavlL.cells5 in Hcells. unfold PavlL.cells5 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlL.regs0 PavlL.regs_out5 60 KS_avlL_5 KS_avlL_5_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlL.regs_out5 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlL.regs_out5]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. left.
    change (SR.ps_pc PavlL.ps6) with 0xb3300 in Hms. change (SR.ps_regs PavlL.ps6) with (map (fun i => (i, nth i PavlL.regs_out6 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlL.ps6) with PavlL.cells6 in Hcells. unfold PavlL.cells6 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlL.regs0 PavlL.regs_out6 60 KS_avlL_6 KS_avlL_6_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlL.regs_out6 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlL.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. left.
    change (SR.ps_pc PavlL.ps7) with 0xb3300 in Hms. change (SR.ps_regs PavlL.ps7) with (map (fun i => (i, nth i PavlL.regs_out7 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlL.ps7) with PavlL.cells7 in Hcells. unfold PavlL.cells7 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlL.regs0 PavlL.regs_out7 60 KS_avlL_7 KS_avlL_7_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlL.regs_out7 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlL.regs_out7]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. right. left.
    change (SR.ps_pc PavlL.ps8) with 0xb3234 in Hms. change (SR.ps_regs PavlL.ps8) with (map (fun i => (i, nth i PavlL.regs_out8 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlL.ps8) with PavlL.cells8 in Hcells. unfold PavlL.cells8 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlL.regs0 PavlL.regs_out8 60 KS_avlL_8 KS_avlL_8_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlL.regs_out8 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlL.regs_out8]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. right. right. left.
    change (SR.ps_pc PavlL.ps9) with 0xb3300 in Hms. change (SR.ps_regs PavlL.ps9) with (map (fun i => (i, nth i PavlL.regs_out9 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlL.ps9) with PavlL.cells9 in Hcells. unfold PavlL.cells9 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlL.regs0 PavlL.regs_out9 60 KS_avlL_9 KS_avlL_9_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlL.regs_out9 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlL.regs_out9]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. right. right. right. left.
    change (SR.ps_pc PavlL.ps10) with 0xb3234 in Hms. change (SR.ps_regs PavlL.ps10) with (map (fun i => (i, nth i PavlL.regs_out10 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlL.ps10) with PavlL.cells10 in Hcells. unfold PavlL.cells10 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlL.regs0 PavlL.regs_out10 60 KS_avlL_10 KS_avlL_10_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlL.regs_out10 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlL.regs_out10]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. right. right. right. right. left.
    change (SR.ps_pc PavlL.ps11) with 0xb3300 in Hms. change (SR.ps_regs PavlL.ps11) with (map (fun i => (i, nth i PavlL.regs_out11 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlL.ps11) with PavlL.cells11 in Hcells. unfold PavlL.cells11 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlL.regs0 PavlL.regs_out11 60 KS_avlL_11 KS_avlL_11_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlL.regs_out11 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlL.regs_out11]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. right. right. right. right. right. left.
    change (SR.ps_pc PavlL.ps12) with 0xb3234 in Hms. change (SR.ps_regs PavlL.ps12) with (map (fun i => (i, nth i PavlL.regs_out12 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlL.ps12) with PavlL.cells12 in Hcells. unfold PavlL.cells12 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlL.regs0 PavlL.regs_out12 60 KS_avlL_12 KS_avlL_12_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlL.regs_out12 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlL.regs_out12]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. right. right. right. right. right. right. 
    change (SR.ps_pc PavlL.ps13) with 0xb3300 in Hms. change (SR.ps_regs PavlL.ps13) with (map (fun i => (i, nth i PavlL.regs_out13 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlL.ps13) with PavlL.cells13 in Hcells. unfold PavlL.cells13 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlL.regs0 PavlL.regs_out13 60 KS_avlL_13 KS_avlL_13_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlL.regs_out13 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlL.regs_out13]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavlB := LibSegBa_avlB_b.
Definition KS_avlB_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavlB.regs0 PavlB.regs_out0).
Lemma KS_avlB_0_ok : BG.kept_ok 60 PavlB.regs0 PavlB.regs_out0 KS_avlB_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlB_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavlB.regs0 PavlB.regs_out1).
Lemma KS_avlB_1_ok : BG.kept_ok 60 PavlB.regs0 PavlB.regs_out1 KS_avlB_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 2 -> getr R (reg 7) = Z_to_bv 64 (-65) -> getr R (reg 8) = Z_to_bv 64 159 -> getr R (reg 9) = Z_to_bv 64 240 -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 14) = Z_to_bv 64 8 -> getr R (reg 15) = Z_to_bv 64 18446744073709551615 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 145280 -> getr R (reg 19) = Z_to_bv 64 18446744073709406335 -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 144 -> getr R (reg 22) = Z_to_bv 64 244 -> getr R (reg 23) = Z_to_bv 64 143 -> getr R (reg 24) = Z_to_bv 64 3 -> getr R (reg 26) = Z_to_bv 64 (V 33%nat) -> getr R (reg 28) = Z_to_bv 64 239 -> getr R (reg 29) = Z_to_bv 64 224 -> getr R (reg 30) = Z_to_bv 64 160 -> getr R (reg 31) = Z_to_bv 64 237 ->
  0 <= (V 33%nat) <= 140737488355328 -> 0 <= (V 35%nat) <= 140737488355328 -> 0 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb3234 M) (st fx' R' 0xb3300 M')
        /\ (forall x, In x KS_avlB_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + (V 35%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ (((V 33%nat) - (((V 33%nat) + (V 35%nat)) mod 2 ^ 64)) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0xb3234 M) (st fx' R' 0xb3004 M')
        /\ (forall x, In x KS_avlB_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ 1 <= (((V 33%nat) - (((V 33%nat) + (V 35%nat)) mod 2 ^ 64)) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G5 G6 G7 G8 G9 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G26 G28 G29 G30 G31 pvzI4 pvzI5 pvzI6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K1l; move K1l before pvzI5; pose proof (proj2 pvzI5) as K1r; move K1r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K2l; move K2l before pvzI6; pose proof (proj2 pvzI6) as K2r; move K2r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 36%nat. }
  assert (HR: regs_ok E PavlB.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlB.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlB.kn0).
  { unfold know_ok, PavlB.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlB.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlB.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavlB.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavlB.ps0) with 0xb3300 in Hms. change (SR.ps_regs PavlB.ps0) with (map (fun i => (i, nth i PavlB.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlB.ps0) with PavlB.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlB.regs0 PavlB.regs_out0 60 KS_avlB_0 KS_avlB_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlB.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavlB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavlB.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavlB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  - right.
    change (SR.ps_pc PavlB.ps1) with 0xb3004 in Hms. change (SR.ps_regs PavlB.ps1) with (map (fun i => (i, nth i PavlB.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavlB.ps1) with PavlB.cells1 in Hcells. unfold PavlB.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlB.regs0 PavlB.regs_out1 60 KS_avlB_1 KS_avlB_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavlB.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PavlB.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavlX := LibSegBa_avlX_b.
Definition KS_avlX : list nat := Eval vm_compute in (BG.kept_list 60 PavlX.regs0 PavlX.regs_out0).
Lemma KS_avlX_ok : BG.kept_ok 60 PavlX.regs0 PavlX.regs_out0 KS_avlX = true. Proof. vm_compute. reflexivity. Qed.
Lemma avlX_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) ->
  140735332487264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 41%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 52%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3300 M) (st fx' R' 0xb3338 M')
        /\ (forall x, In x KS_avlX -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 52%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 G2 pvzI15 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV40l; move HV40l before pvzI2; pose proof (proj2 pvzI2) as HV40r; move HV40r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV41l; move HV41l before pvzI3; pose proof (proj2 pvzI3) as HV41r; move HV41r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV42l; move HV42l before pvzI4; pose proof (proj2 pvzI4) as HV42r; move HV42r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV43l; move HV43l before pvzI5; pose proof (proj2 pvzI5) as HV43r; move HV43r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV44l; move HV44l before pvzI6; pose proof (proj2 pvzI6) as HV44r; move HV44r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV45l; move HV45l before pvzI7; pose proof (proj2 pvzI7) as HV45r; move HV45r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV46l; move HV46l before pvzI8; pose proof (proj2 pvzI8) as HV46r; move HV46r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV47l; move HV47l before pvzI9; pose proof (proj2 pvzI9) as HV47r; move HV47r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV48l; move HV48l before pvzI10; pose proof (proj2 pvzI10) as HV48r; move HV48r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV49l; move HV49l before pvzI11; pose proof (proj2 pvzI11) as HV49r; move HV49r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV50l; move HV50l before pvzI12; pose proof (proj2 pvzI12) as HV50r; move HV50r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV51l; move HV51l before pvzI13; pose proof (proj2 pvzI13) as HV51r; move HV51r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV52l; move HV52l before pvzI14; pose proof (proj2 pvzI14) as HV52r; move HV52r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K0l; move K0l before pvzI15; pose proof (proj2 pvzI15) as K0r; move K0r before pvzI15; clear pvzI15.
  set (vz_2 := V 2%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 40%nat => vz_40 | 41%nat => vz_41 | 42%nat => vz_42 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 53%nat. }
  assert (HR: regs_ok E PavlX.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavlX.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavlX.kn0).
  { unfold know_ok, PavlX.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV41l HV41r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K14]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavlX.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavlX.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavlX.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PavlX.ps0) with 0xb3338 in Hms. change (SR.ps_regs PavlX.ps0) with (map (fun i => (i, nth i PavlX.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PavlX.ps0) with PavlX.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PavlX.regs0 PavlX.regs_out0 60 KS_avlX KS_avlX_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PavlX.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PavlX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavlX.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PavlX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavlX.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PavlX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavlX.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PavlX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavlX.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PavlX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavlX.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PavlX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavlX.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PavlX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavlX.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PavlX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavlX.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PavlX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavlX.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PavlX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavlX.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PavlX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavlX.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PavlX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavlX.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PavlX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PavlX.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PavlX.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

End PMAVALP1.
