(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BigLinkZA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0PlanKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanPlanCore
     BigLinkBase. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import BigLinkGlue_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import L5Kn_u L5KnA_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.seg Require LibSegBs_vaE_u LibSegBs_vaEz_u LibSegBs_vaF8_u LibSegBs_vaF1_u LibSegBs_vaS2_0_u LibSegBs_vaS2_1a_u LibSegBs_vaS2_1b_u LibSegBs_vaS2_2a_u LibSegBs_vaS2_2b_u LibSegBs_vaS2_3a_u LibSegBs_vaS2_3b_u LibSegBs_vaS2_big_u LibSegBs_vaB_u LibSegBs_vaX_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PMVAP.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).

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
Module PvaE := LibSegBs_vaE_u.
Definition KS_vaE_0 : list nat := Eval vm_compute in (BG.kept_list 60 PvaE.regs0 PvaE.regs_out0).
Lemma KS_vaE_0_ok : BG.kept_ok 60 PvaE.regs0 PvaE.regs_out0 KS_vaE_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaE_1 : list nat := Eval vm_compute in (BG.kept_list 60 PvaE.regs0 PvaE.regs_out1).
Lemma KS_vaE_1_ok : BG.kept_ok 60 PvaE.regs0 PvaE.regs_out1 KS_vaE_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vaE_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 35%nat) ->
  140735332483168 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 -> 1 <= (V 33%nat) <= 140737488355328 ->
  0 <= (V 35%nat) <= 67108863 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 96) <= bv_unsigned a < ((V 2%nat) - 96) + 96) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 96) <= i < ((V 2%nat) - 96) + 96) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x384bc M) (st fx' R' 0x38714 M')
        /\ (forall x, In x KS_vaE_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + (V 35%nat))
        /\ getr R' (reg 13) = Z_to_bv 64 1
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ (((V 35%nat) - 0) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0x384bc M) (st fx' R' 0x3855c M')
        /\ (forall x, In x KS_vaE_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 96)
        /\ getr R' (reg 5) = Z_to_bv 64 2
        /\ getr R' (reg 6) = Z_to_bv 64 18446744073709551551
        /\ getr R' (reg 7) = Z_to_bv 64 239
        /\ getr R' (reg 8) = Z_to_bv 64 240
        /\ getr R' (reg 9) = Z_to_bv 64 144
        /\ getr R' (reg 11) = Z_to_bv 64 79124
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + (V 35%nat))
        /\ getr R' (reg 13) = Z_to_bv 64 8
        /\ getr R' (reg 14) = Z_to_bv 64 18446744073709551615
        /\ getr R' (reg 15) = Z_to_bv 64 1
        /\ getr R' (reg 16) = Z_to_bv 64 18446744073709551554
        /\ getr R' (reg 17) = Z_to_bv 64 245
        /\ getr R' (reg 18) = Z_to_bv 64 244
        /\ getr R' (reg 19) = Z_to_bv 64 143
        /\ getr R' (reg 20) = Z_to_bv 64 80240
        /\ getr R' (reg 21) = Z_to_bv 64 18446744073709471375
        /\ getr R' (reg 22) = Z_to_bv 64 3
        /\ getr R' (reg 28) = Z_to_bv 64 224
        /\ getr R' (reg 29) = Z_to_bv 64 160
        /\ getr R' (reg 30) = Z_to_bv 64 237
        /\ getr R' (reg 31) = Z_to_bv 64 159
        /\ 1 <= (((V 35%nat) - 0) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (bv_unsigned (getr R (reg 27)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (bv_unsigned (getr R (reg 26)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (bv_unsigned (getr R (reg 25)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 8))))).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G10 G11 pvzI4 K1 K2 pvzI5 pvzI6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K3l; move K3l before pvzI5; pose proof (proj2 pvzI5) as K3r; move K3r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K4l; move K4l before pvzI6; pose proof (proj2 pvzI6) as K4r; move K4r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 36%nat. }
  assert (HR: regs_ok E PvaE.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvaE.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvaE.kn0).
  { unfold know_ok, PvaE.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvaE.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvaE.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 96) <= bv_unsigned a < (vz_2 - 96) + 96) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PvaE.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PvaE.ps0) with 0x38714 in Hms. change (SR.ps_regs PvaE.ps0) with (map (fun i => (i, nth i PvaE.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaE.ps0) with PvaE.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaE.regs0 PvaE.regs_out0 60 KS_vaE_0 KS_vaE_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaE.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvaE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaE.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PvaE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaE.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PvaE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  - right.
    change (SR.ps_pc PvaE.ps1) with 0x3855c in Hms. change (SR.ps_regs PvaE.ps1) with (map (fun i => (i, nth i PvaE.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaE.ps1) with PvaE.cells1 in Hcells. unfold PvaE.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaE.regs0 PvaE.regs_out1 60 KS_vaE_1 KS_vaE_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaE.regs_out1 E' R' 2 Hregs) by (clear; lia). cbn [nth PvaE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaE.regs_out1 E' R' 5 Hregs) by (clear; lia). cbn [nth PvaE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaE.regs_out1 E' R' 6 Hregs) by (clear; lia). cbn [nth PvaE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaE.regs_out1 E' R' 7 Hregs) by (clear; lia). cbn [nth PvaE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaE.regs_out1 E' R' 8 Hregs) by (clear; lia). cbn [nth PvaE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaE.regs_out1 E' R' 9 Hregs) by (clear; lia). cbn [nth PvaE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaE.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaE.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PvaE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaE.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PvaE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaE.regs_out1 E' R' 14 Hregs) by (clear; lia). cbn [nth PvaE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaE.regs_out1 E' R' 15 Hregs) by (clear; lia). cbn [nth PvaE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaE.regs_out1 E' R' 16 Hregs) by (clear; lia). cbn [nth PvaE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaE.regs_out1 E' R' 17 Hregs) by (clear; lia). cbn [nth PvaE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaE.regs_out1 E' R' 18 Hregs) by (clear; lia). cbn [nth PvaE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaE.regs_out1 E' R' 19 Hregs) by (clear; lia). cbn [nth PvaE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaE.regs_out1 E' R' 20 Hregs) by (clear; lia). cbn [nth PvaE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaE.regs_out1 E' R' 21 Hregs) by (clear; lia). cbn [nth PvaE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaE.regs_out1 E' R' 22 Hregs) by (clear; lia). cbn [nth PvaE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaE.regs_out1 E' R' 28 Hregs) by (clear; lia). cbn [nth PvaE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaE.regs_out1 E' R' 29 Hregs) by (clear; lia). cbn [nth PvaE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaE.regs_out1 E' R' 30 Hregs) by (clear; lia). cbn [nth PvaE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaE.regs_out1 E' R' 31 Hregs) by (clear; lia). cbn [nth PvaE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

Module PvaEz := LibSegBs_vaEz_u.
Definition KS_vaEz : list nat := Eval vm_compute in (BG.kept_list 60 PvaEz.regs0 PvaEz.regs_out0).
Lemma KS_vaEz_ok : BG.kept_ok 60 PvaEz.regs0 PvaEz.regs_out0 KS_vaEz = true. Proof. vm_compute. reflexivity. Qed.
Lemma vaEz_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 35%nat) ->
  140735332483168 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 -> 0 <= (V 33%nat) <= 0 ->
  0 <= (V 35%nat) <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 96) <= bv_unsigned a < ((V 2%nat) - 96) + 96) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 96) <= i < ((V 2%nat) - 96) + 96) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x384bc M) (st fx' R' 0x38714 M')
        /\ (forall x, In x KS_vaEz -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 1
        /\ getr R' (reg 14) = Z_to_bv 64 1).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G10 G11 pvzI4 K1 K2 pvzI5 pvzI6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K3l; move K3l before pvzI5; pose proof (proj2 pvzI5) as K3r; move K3r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K4l; move K4l before pvzI6; pose proof (proj2 pvzI6) as K4r; move K4r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 36%nat. }
  assert (HR: regs_ok E PvaEz.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvaEz.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvaEz.kn0).
  { unfold know_ok, PvaEz.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvaEz.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvaEz.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 96) <= bv_unsigned a < (vz_2 - 96) + 96) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PvaEz.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvaEz.ps0) with 0x38714 in Hms. change (SR.ps_regs PvaEz.ps0) with (map (fun i => (i, nth i PvaEz.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvaEz.ps0) with PvaEz.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaEz.regs0 PvaEz.regs_out0 60 KS_vaEz KS_vaEz_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvaEz.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvaEz.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvaEz.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PvaEz.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvaEz.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PvaEz.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.

(* [comment removed for export] *)
Module PvaF8 := LibSegBs_vaF8_u.
Definition KS_vaF8_0 : list nat := Eval vm_compute in (BG.kept_list 60 PvaF8.regs0 PvaF8.regs_out0).
Lemma KS_vaF8_0_ok : BG.kept_ok 60 PvaF8.regs0 PvaF8.regs_out0 KS_vaF8_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaF8_1 : list nat := Eval vm_compute in (BG.kept_list 60 PvaF8.regs0 PvaF8.regs_out1).
Lemma KS_vaF8_1_ok : BG.kept_ok 60 PvaF8.regs0 PvaF8.regs_out1 KS_vaF8_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaF8_2 : list nat := Eval vm_compute in (BG.kept_list 60 PvaF8.regs0 PvaF8.regs_out2).
Lemma KS_vaF8_2_ok : BG.kept_ok 60 PvaF8.regs0 PvaF8.regs_out2 KS_vaF8_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaF8_3 : list nat := Eval vm_compute in (BG.kept_list 60 PvaF8.regs0 PvaF8.regs_out3).
Lemma KS_vaF8_3_ok : BG.kept_ok 60 PvaF8.regs0 PvaF8.regs_out3 KS_vaF8_3 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaF8_4 : list nat := Eval vm_compute in (BG.kept_list 60 PvaF8.regs0 PvaF8.regs_out4).
Lemma KS_vaF8_4_ok : BG.kept_ok 60 PvaF8.regs0 PvaF8.regs_out4 KS_vaF8_4 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaF8_5 : list nat := Eval vm_compute in (BG.kept_list 60 PvaF8.regs0 PvaF8.regs_out5).
Lemma KS_vaF8_5_ok : BG.kept_ok 60 PvaF8.regs0 PvaF8.regs_out5 KS_vaF8_5 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaF8_6 : list nat := Eval vm_compute in (BG.kept_list 60 PvaF8.regs0 PvaF8.regs_out6).
Lemma KS_vaF8_6_ok : BG.kept_ok 60 PvaF8.regs0 PvaF8.regs_out6 KS_vaF8_6 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaF8_7 : list nat := Eval vm_compute in (BG.kept_list 60 PvaF8.regs0 PvaF8.regs_out7).
Lemma KS_vaF8_7_ok : BG.kept_ok 60 PvaF8.regs0 PvaF8.regs_out7 KS_vaF8_7 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaF8_8 : list nat := Eval vm_compute in (BG.kept_list 60 PvaF8.regs0 PvaF8.regs_out8).
Lemma KS_vaF8_8_ok : BG.kept_ok 60 PvaF8.regs0 PvaF8.regs_out8 KS_vaF8_8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vaF8_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 2 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 13) = Z_to_bv 64 8 -> getr R (reg 14) = Z_to_bv 64 (-1) -> getr R (reg 15) = Z_to_bv 64 1 -> getr R (reg 16) = Z_to_bv 64 (-62) -> getr R (reg 17) = Z_to_bv 64 245 -> getr R (reg 18) = Z_to_bv 64 244 -> getr R (reg 19) = Z_to_bv 64 143 -> getr R (reg 20) = Z_to_bv 64 80240 -> getr R (reg 21) = Z_to_bv 64 (-80241) -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  1 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M (V 33%nat) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((V 33%nat) + 1) (V 37%nat) -> 0 <= (V 37%nat) <= 255 -> L5.u8_at RSEGS M ((V 33%nat) + 2) (V 38%nat) ->
  0 <= (V 38%nat) <= 255 -> L5.u8_at RSEGS M ((V 33%nat) + 3) (V 39%nat) -> 0 <= (V 39%nat) <= 255 -> L5.u8_at RSEGS M ((V 33%nat) + 4) (V 40%nat) ->
  0 <= (V 40%nat) <= 255 -> L5.u8_at RSEGS M ((V 33%nat) + 5) (V 41%nat) -> 0 <= (V 41%nat) <= 255 -> L5.u8_at RSEGS M ((V 33%nat) + 6) (V 42%nat) ->
  0 <= (V 42%nat) <= 255 -> L5.u8_at RSEGS M ((V 33%nat) + 7) (V 43%nat) -> 0 <= (V 43%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x3855c M) (st fx' R' 0x38600 M')
        /\ (forall x, In x KS_vaF8_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 36%nat) + 80240)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 36%nat))
      \/ (msteps RSEGS (st fx R 0x3855c M) (st fx' R' 0x38600 M')
        /\ (forall x, In x KS_vaF8_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 37%nat) + 80240)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 37%nat))
      \/ (msteps RSEGS (st fx R 0x3855c M) (st fx' R' 0x38600 M')
        /\ (forall x, In x KS_vaF8_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 38%nat) + 80240)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 38%nat))
      \/ (msteps RSEGS (st fx R 0x3855c M) (st fx' R' 0x38600 M')
        /\ (forall x, In x KS_vaF8_3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 39%nat) + 80240)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 39%nat))
      \/ (msteps RSEGS (st fx R 0x3855c M) (st fx' R' 0x38600 M')
        /\ (forall x, In x KS_vaF8_4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 4)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + 80240)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 40%nat))
      \/ (msteps RSEGS (st fx R 0x3855c M) (st fx' R' 0x38600 M')
        /\ (forall x, In x KS_vaF8_5 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 41%nat) + 80240)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 41%nat))
      \/ (msteps RSEGS (st fx R 0x3855c M) (st fx' R' 0x38600 M')
        /\ (forall x, In x KS_vaF8_6 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 42%nat) + 80240)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 42%nat))
      \/ (msteps RSEGS (st fx R 0x3855c M) (st fx' R' 0x38600 M')
        /\ (forall x, In x KS_vaF8_7 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 43%nat) + 80240)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 43%nat))
      \/ (msteps RSEGS (st fx R 0x3855c M) (st fx' R' 0x386b8 M')
        /\ (forall x, In x KS_vaF8_8 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 8))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 G2 G5 G6 G7 G8 G9 G10 G12 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G28 G29 G30 G31 pvzI12 pvzI13 pvzI14 K3 pvzI15 K5 pvzI16 K7 pvzI17 K9 pvzI18 K11 pvzI19 K13 pvzI20 K15 pvzI21 K17 pvzI22.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV39l; move HV39l before pvzI7; pose proof (proj2 pvzI7) as HV39r; move HV39r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV40l; move HV40l before pvzI8; pose proof (proj2 pvzI8) as HV40r; move HV40r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV41l; move HV41l before pvzI9; pose proof (proj2 pvzI9) as HV41r; move HV41r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV42l; move HV42l before pvzI10; pose proof (proj2 pvzI10) as HV42r; move HV42r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV43l; move HV43l before pvzI11; pose proof (proj2 pvzI11) as HV43r; move HV43r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K0l; move K0l before pvzI12; pose proof (proj2 pvzI12) as K0r; move K0r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K1l; move K1l before pvzI13; pose proof (proj2 pvzI13) as K1r; move K1r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K2l; move K2l before pvzI14; pose proof (proj2 pvzI14) as K2r; move K2r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K4l; move K4l before pvzI15; pose proof (proj2 pvzI15) as K4r; move K4r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K6l; move K6l before pvzI16; pose proof (proj2 pvzI16) as K6r; move K6r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K8l; move K8l before pvzI17; pose proof (proj2 pvzI17) as K8r; move K8r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K10l; move K10l before pvzI18; pose proof (proj2 pvzI18) as K10r; move K10r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K12l; move K12l before pvzI19; pose proof (proj2 pvzI19) as K12r; move K12r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K14l; move K14l before pvzI20; pose proof (proj2 pvzI20) as K14r; move K14r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K16l; move K16l before pvzI21; pose proof (proj2 pvzI21) as K16r; move K16r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K18l; move K18l before pvzI22; pose proof (proj2 pvzI22) as K18r; move K18r before pvzI22; clear pvzI22.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 41%nat => vz_41 | 42%nat => vz_42 | 43%nat => vz_43 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E PvaF8.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvaF8.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvaF8.kn0).
  { unfold know_ok, PvaF8.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV37l HV37r K6l K6r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV37l HV37r K6l K6r) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV38l HV38r K8l K8r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV38l HV38r K8l K8r) | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV39l HV39r K10l K10r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV39l HV39r K10l K10r) | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV40l HV40r K12l K12r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV40l HV40r K12l K12r) | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K12l K12r) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV41l HV41r K14l K14r) | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV42l HV42r K16l K16r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV42l HV42r K16l K16r) | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV43l HV43r K18l K18r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV43l HV43r K18l K18r) | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K18l K18r) | exact (conj K18l K18r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvaF8.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvaF8.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvaF8.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PvaF8.ps0) with 0x38600 in Hms. change (SR.ps_regs PvaF8.ps0) with (map (fun i => (i, nth i PvaF8.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaF8.ps0) with PvaF8.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaF8.regs0 PvaF8.regs_out0 60 KS_vaF8_0 KS_vaF8_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaF8.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaF8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PvaF8.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PvaF8.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. left.
    change (SR.ps_pc PvaF8.ps1) with 0x38600 in Hms. change (SR.ps_regs PvaF8.ps1) with (map (fun i => (i, nth i PvaF8.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaF8.ps1) with PvaF8.cells1 in Hcells. unfold PvaF8.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaF8.regs0 PvaF8.regs_out1 60 KS_vaF8_1 KS_vaF8_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaF8.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PvaF8.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaF8.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaF8.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PvaF8.regs_out1 E' R' 24 Hregs) by (clear; lia). cbn [nth PvaF8.regs_out1]. first [reflexivity | wordP' ZA Hag]. 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. left.
    change (SR.ps_pc PvaF8.ps2) with 0x38600 in Hms. change (SR.ps_regs PvaF8.ps2) with (map (fun i => (i, nth i PvaF8.regs_out2 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaF8.ps2) with PvaF8.cells2 in Hcells. unfold PvaF8.cells2 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaF8.regs0 PvaF8.regs_out2 60 KS_vaF8_2 KS_vaF8_2_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaF8.regs_out2 E' R' 10 Hregs) by (clear; lia). cbn [nth PvaF8.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaF8.regs_out2 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaF8.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PvaF8.regs_out2 E' R' 24 Hregs) by (clear; lia). cbn [nth PvaF8.regs_out2]. first [reflexivity | wordP' ZA Hag]. 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. left.
    change (SR.ps_pc PvaF8.ps3) with 0x38600 in Hms. change (SR.ps_regs PvaF8.ps3) with (map (fun i => (i, nth i PvaF8.regs_out3 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaF8.ps3) with PvaF8.cells3 in Hcells. unfold PvaF8.cells3 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaF8.regs0 PvaF8.regs_out3 60 KS_vaF8_3 KS_vaF8_3_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaF8.regs_out3 E' R' 10 Hregs) by (clear; lia). cbn [nth PvaF8.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaF8.regs_out3 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaF8.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PvaF8.regs_out3 E' R' 24 Hregs) by (clear; lia). cbn [nth PvaF8.regs_out3]. first [reflexivity | wordP' ZA Hag]. 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. left.
    change (SR.ps_pc PvaF8.ps4) with 0x38600 in Hms. change (SR.ps_regs PvaF8.ps4) with (map (fun i => (i, nth i PvaF8.regs_out4 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaF8.ps4) with PvaF8.cells4 in Hcells. unfold PvaF8.cells4 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaF8.regs0 PvaF8.regs_out4 60 KS_vaF8_4 KS_vaF8_4_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaF8.regs_out4 E' R' 10 Hregs) by (clear; lia). cbn [nth PvaF8.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaF8.regs_out4 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaF8.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PvaF8.regs_out4 E' R' 24 Hregs) by (clear; lia). cbn [nth PvaF8.regs_out4]. first [reflexivity | wordP' ZA Hag]. 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. left.
    change (SR.ps_pc PvaF8.ps5) with 0x38600 in Hms. change (SR.ps_regs PvaF8.ps5) with (map (fun i => (i, nth i PvaF8.regs_out5 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaF8.ps5) with PvaF8.cells5 in Hcells. unfold PvaF8.cells5 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaF8.regs0 PvaF8.regs_out5 60 KS_vaF8_5 KS_vaF8_5_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaF8.regs_out5 E' R' 10 Hregs) by (clear; lia). cbn [nth PvaF8.regs_out5]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaF8.regs_out5 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaF8.regs_out5]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PvaF8.regs_out5 E' R' 24 Hregs) by (clear; lia). cbn [nth PvaF8.regs_out5]. first [reflexivity | wordP' ZA Hag]. 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. left.
    change (SR.ps_pc PvaF8.ps6) with 0x38600 in Hms. change (SR.ps_regs PvaF8.ps6) with (map (fun i => (i, nth i PvaF8.regs_out6 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaF8.ps6) with PvaF8.cells6 in Hcells. unfold PvaF8.cells6 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaF8.regs0 PvaF8.regs_out6 60 KS_vaF8_6 KS_vaF8_6_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaF8.regs_out6 E' R' 10 Hregs) by (clear; lia). cbn [nth PvaF8.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaF8.regs_out6 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaF8.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PvaF8.regs_out6 E' R' 24 Hregs) by (clear; lia). cbn [nth PvaF8.regs_out6]. first [reflexivity | wordP' ZA Hag]. 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. left.
    change (SR.ps_pc PvaF8.ps7) with 0x38600 in Hms. change (SR.ps_regs PvaF8.ps7) with (map (fun i => (i, nth i PvaF8.regs_out7 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaF8.ps7) with PvaF8.cells7 in Hcells. unfold PvaF8.cells7 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaF8.regs0 PvaF8.regs_out7 60 KS_vaF8_7 KS_vaF8_7_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaF8.regs_out7 E' R' 10 Hregs) by (clear; lia). cbn [nth PvaF8.regs_out7]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaF8.regs_out7 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaF8.regs_out7]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PvaF8.regs_out7 E' R' 24 Hregs) by (clear; lia). cbn [nth PvaF8.regs_out7]. first [reflexivity | wordP' ZA Hag]. 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. right. 
    change (SR.ps_pc PvaF8.ps8) with 0x386b8 in Hms. change (SR.ps_regs PvaF8.ps8) with (map (fun i => (i, nth i PvaF8.regs_out8 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaF8.ps8) with PvaF8.cells8 in Hcells. unfold PvaF8.cells8 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaF8.regs0 PvaF8.regs_out8 60 KS_vaF8_8 KS_vaF8_8_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaF8.regs_out8 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaF8.regs_out8]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PvaF8.regs_out8 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaF8.regs_out8]. first [reflexivity | wordP' ZA Hag]. 
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvaF1 := LibSegBs_vaF1_u.
Definition KS_vaF1 : list nat := Eval vm_compute in (BG.kept_list 60 PvaF1.regs0 PvaF1.regs_out0).
Lemma KS_vaF1_ok : BG.kept_ok 60 PvaF1.regs0 PvaF1.regs_out0 KS_vaF1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vaF1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 2 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 13) = Z_to_bv 64 8 -> getr R (reg 14) = Z_to_bv 64 (-1) -> getr R (reg 15) = Z_to_bv 64 1 -> getr R (reg 16) = Z_to_bv 64 (-62) -> getr R (reg 17) = Z_to_bv 64 245 -> getr R (reg 18) = Z_to_bv 64 244 -> getr R (reg 19) = Z_to_bv 64 143 -> getr R (reg 20) = Z_to_bv 64 80240 -> getr R (reg 21) = Z_to_bv 64 (-80241) -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  1 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 7 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M (V 33%nat) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3855c M) (st fx' R' 0x38600 M')
        /\ (forall x, In x KS_vaF1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 36%nat) + 80240)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 36%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G12 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PvaF1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvaF1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvaF1.kn0).
  { unfold know_ok, PvaF1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvaF1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvaF1.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvaF1.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvaF1.ps0) with 0x38600 in Hms. change (SR.ps_regs PvaF1.ps0) with (map (fun i => (i, nth i PvaF1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvaF1.ps0) with PvaF1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaF1.regs0 PvaF1.regs_out0 60 KS_vaF1 KS_vaF1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvaF1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaF1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvaF1.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PvaF1.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvaS2_0 := LibSegBs_vaS2_0_u.
Definition KS_vaS2_0_0 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_0.regs0 PvaS2_0.regs_out0).
Lemma KS_vaS2_0_0_ok : BG.kept_ok 60 PvaS2_0.regs0 PvaS2_0.regs_out0 KS_vaS2_0_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_0_1 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_0.regs0 PvaS2_0.regs_out1).
Lemma KS_vaS2_0_1_ok : BG.kept_ok 60 PvaS2_0.regs0 PvaS2_0.regs_out1 KS_vaS2_0_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_0_2 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_0.regs0 PvaS2_0.regs_out2).
Lemma KS_vaS2_0_2_ok : BG.kept_ok 60 PvaS2_0.regs0 PvaS2_0.regs_out2 KS_vaS2_0_2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vaS2_0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 2 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 13) = Z_to_bv 64 8 -> getr R (reg 14) = Z_to_bv 64 (-1) -> getr R (reg 15) = Z_to_bv 64 1 -> getr R (reg 16) = Z_to_bv 64 (-62) -> getr R (reg 17) = Z_to_bv 64 245 -> getr R (reg 18) = Z_to_bv 64 244 -> getr R (reg 19) = Z_to_bv 64 143 -> getr R (reg 20) = Z_to_bv 64 80240 -> getr R (reg 21) = Z_to_bv 64 (-80241) -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 24) = Z_to_bv 64 (V 37%nat) -> getr R (reg 25) = Z_to_bv 64 0 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386e0 M')
        /\ (forall x, In x KS_vaS2_0_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 33%nat))
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386b8 M')
        /\ (forall x, In x KS_vaS2_0_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 33%nat)
        /\ (V 37%nat) < 245)
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386e0 M')
        /\ (forall x, In x KS_vaS2_0_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 33%nat)
        /\ 245 <= (V 37%nat))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G12 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G24 G25 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 pvzI8.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PvaS2_0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvaS2_0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvaS2_0.kn0).
  { unfold know_ok, PvaS2_0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvaS2_0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvaS2_0.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvaS2_0.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PvaS2_0.ps0) with 0x386e0 in Hms. change (SR.ps_regs PvaS2_0.ps0) with (map (fun i => (i, nth i PvaS2_0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_0.ps0) with PvaS2_0.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_0.regs0 PvaS2_0.regs_out0 60 KS_vaS2_0_0 KS_vaS2_0_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaS2_0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_0.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PvaS2_0.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_0.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. left.
    change (SR.ps_pc PvaS2_0.ps1) with 0x386b8 in Hms. change (SR.ps_regs PvaS2_0.ps1) with (map (fun i => (i, nth i PvaS2_0.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_0.ps1) with PvaS2_0.cells1 in Hcells. unfold PvaS2_0.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_0.regs0 PvaS2_0.regs_out1 60 KS_vaS2_0_1 KS_vaS2_0_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_0.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaS2_0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_0.regs_out1 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_0.regs_out1 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. 
    change (SR.ps_pc PvaS2_0.ps2) with 0x386e0 in Hms. change (SR.ps_regs PvaS2_0.ps2) with (map (fun i => (i, nth i PvaS2_0.regs_out2 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_0.ps2) with PvaS2_0.cells2 in Hcells. unfold PvaS2_0.cells2 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_0.regs0 PvaS2_0.regs_out2 60 KS_vaS2_0_2 KS_vaS2_0_2_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_0.regs_out2 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaS2_0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_0.regs_out2 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_0.regs_out2 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvaS2_1a := LibSegBs_vaS2_1a_u.
Definition KS_vaS2_1a : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_1a.regs0 PvaS2_1a.regs_out0).
Lemma KS_vaS2_1a_ok : BG.kept_ok 60 PvaS2_1a.regs0 PvaS2_1a.regs_out0 KS_vaS2_1a = true. Proof. vm_compute. reflexivity. Qed.
Lemma vaS2_1a_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 2 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 13) = Z_to_bv 64 8 -> getr R (reg 14) = Z_to_bv 64 (-1) -> getr R (reg 15) = Z_to_bv 64 1 -> getr R (reg 16) = Z_to_bv 64 (-62) -> getr R (reg 17) = Z_to_bv 64 245 -> getr R (reg 18) = Z_to_bv 64 244 -> getr R (reg 19) = Z_to_bv 64 143 -> getr R (reg 20) = Z_to_bv 64 80240 -> getr R (reg 21) = Z_to_bv 64 (-80241) -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 24) = Z_to_bv 64 (V 37%nat) -> getr R (reg 25) = Z_to_bv 64 1 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 1 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386e0 M')
        /\ (forall x, In x KS_vaS2_1a -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 5).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G12 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G24 G25 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 pvzI8.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PvaS2_1a.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvaS2_1a.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvaS2_1a.kn0).
  { unfold know_ok, PvaS2_1a.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvaS2_1a.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvaS2_1a.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvaS2_1a.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvaS2_1a.ps0) with 0x386e0 in Hms. change (SR.ps_regs PvaS2_1a.ps0) with (map (fun i => (i, nth i PvaS2_1a.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvaS2_1a.ps0) with PvaS2_1a.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_1a.regs0 PvaS2_1a.regs_out0 60 KS_vaS2_1a KS_vaS2_1a_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg PvaS2_1a.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaS2_1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvaS2_1b := LibSegBs_vaS2_1b_u.
Definition KS_vaS2_1b_0 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_1b.regs0 PvaS2_1b.regs_out0).
Lemma KS_vaS2_1b_0_ok : BG.kept_ok 60 PvaS2_1b.regs0 PvaS2_1b.regs_out0 KS_vaS2_1b_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_1b_1 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_1b.regs0 PvaS2_1b.regs_out1).
Lemma KS_vaS2_1b_1_ok : BG.kept_ok 60 PvaS2_1b.regs0 PvaS2_1b.regs_out1 KS_vaS2_1b_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_1b_2 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_1b.regs0 PvaS2_1b.regs_out2).
Lemma KS_vaS2_1b_2_ok : BG.kept_ok 60 PvaS2_1b.regs0 PvaS2_1b.regs_out2 KS_vaS2_1b_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_1b_3 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_1b.regs0 PvaS2_1b.regs_out3).
Lemma KS_vaS2_1b_3_ok : BG.kept_ok 60 PvaS2_1b.regs0 PvaS2_1b.regs_out3 KS_vaS2_1b_3 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_1b_4 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_1b.regs0 PvaS2_1b.regs_out4).
Lemma KS_vaS2_1b_4_ok : BG.kept_ok 60 PvaS2_1b.regs0 PvaS2_1b.regs_out4 KS_vaS2_1b_4 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_1b_5 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_1b.regs0 PvaS2_1b.regs_out5).
Lemma KS_vaS2_1b_5_ok : BG.kept_ok 60 PvaS2_1b.regs0 PvaS2_1b.regs_out5 KS_vaS2_1b_5 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_1b_6 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_1b.regs0 PvaS2_1b.regs_out6).
Lemma KS_vaS2_1b_6_ok : BG.kept_ok 60 PvaS2_1b.regs0 PvaS2_1b.regs_out6 KS_vaS2_1b_6 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_1b_7 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_1b.regs0 PvaS2_1b.regs_out7).
Lemma KS_vaS2_1b_7_ok : BG.kept_ok 60 PvaS2_1b.regs0 PvaS2_1b.regs_out7 KS_vaS2_1b_7 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_1b_8 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_1b.regs0 PvaS2_1b.regs_out8).
Lemma KS_vaS2_1b_8_ok : BG.kept_ok 60 PvaS2_1b.regs0 PvaS2_1b.regs_out8 KS_vaS2_1b_8 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_1b_9 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_1b.regs0 PvaS2_1b.regs_out9).
Lemma KS_vaS2_1b_9_ok : BG.kept_ok 60 PvaS2_1b.regs0 PvaS2_1b.regs_out9 KS_vaS2_1b_9 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_1b_10 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_1b.regs0 PvaS2_1b.regs_out10).
Lemma KS_vaS2_1b_10_ok : BG.kept_ok 60 PvaS2_1b.regs0 PvaS2_1b.regs_out10 KS_vaS2_1b_10 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_1b_11 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_1b.regs0 PvaS2_1b.regs_out11).
Lemma KS_vaS2_1b_11_ok : BG.kept_ok 60 PvaS2_1b.regs0 PvaS2_1b.regs_out11 KS_vaS2_1b_11 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_1b_12 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_1b.regs0 PvaS2_1b.regs_out12).
Lemma KS_vaS2_1b_12_ok : BG.kept_ok 60 PvaS2_1b.regs0 PvaS2_1b.regs_out12 KS_vaS2_1b_12 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_1b_13 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_1b.regs0 PvaS2_1b.regs_out13).
Lemma KS_vaS2_1b_13_ok : BG.kept_ok 60 PvaS2_1b.regs0 PvaS2_1b.regs_out13 KS_vaS2_1b_13 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_1b_14 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_1b.regs0 PvaS2_1b.regs_out14).
Lemma KS_vaS2_1b_14_ok : BG.kept_ok 60 PvaS2_1b.regs0 PvaS2_1b.regs_out14 KS_vaS2_1b_14 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vaS2_1b_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 2 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 13) = Z_to_bv 64 8 -> getr R (reg 14) = Z_to_bv 64 (-1) -> getr R (reg 15) = Z_to_bv 64 1 -> getr R (reg 16) = Z_to_bv 64 (-62) -> getr R (reg 17) = Z_to_bv 64 245 -> getr R (reg 18) = Z_to_bv 64 244 -> getr R (reg 19) = Z_to_bv 64 143 -> getr R (reg 20) = Z_to_bv 64 80240 -> getr R (reg 21) = Z_to_bv 64 (-80241) -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 24) = Z_to_bv 64 (V 37%nat) -> getr R (reg 25) = Z_to_bv 64 1 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 2 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 1) (V 39%nat) ->
  0 <= (V 39%nat) <= 255 -> 0 <= (V 37%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386e0 M')
        /\ (forall x, In x KS_vaS2_1b_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 2))
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386e0 M')
        /\ (forall x, In x KS_vaS2_1b_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ (((V 37%nat) - 240) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386b8 M')
        /\ (forall x, In x KS_vaS2_1b_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ (((V 37%nat) - 240) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386e0 M')
        /\ (forall x, In x KS_vaS2_1b_3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ (((V 37%nat) - 244) mod 2 ^ 64) < 1
        /\ 1 <= (((V 37%nat) - 240) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386b8 M')
        /\ (forall x, In x KS_vaS2_1b_4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ (((V 37%nat) - 244) mod 2 ^ 64) < 1
        /\ 1 <= (((V 37%nat) - 240) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386e0 M')
        /\ (forall x, In x KS_vaS2_1b_5 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ 1 <= (((V 37%nat) - 244) mod 2 ^ 64)
        /\ 1 <= (((V 37%nat) - 240) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386b8 M')
        /\ (forall x, In x KS_vaS2_1b_6 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ (V 37%nat) < 245
        /\ 1 <= (((V 37%nat) - 244) mod 2 ^ 64)
        /\ 1 <= (((V 37%nat) - 240) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386e0 M')
        /\ (forall x, In x KS_vaS2_1b_7 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ 245 <= (V 37%nat)
        /\ 1 <= (((V 37%nat) - 244) mod 2 ^ 64)
        /\ 1 <= (((V 37%nat) - 240) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386e0 M')
        /\ (forall x, In x KS_vaS2_1b_8 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ (((V 37%nat) - 224) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386b8 M')
        /\ (forall x, In x KS_vaS2_1b_9 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ (((V 37%nat) - 224) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386e0 M')
        /\ (forall x, In x KS_vaS2_1b_10 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ (((V 37%nat) - 237) mod 2 ^ 64) < 1
        /\ 1 <= (((V 37%nat) - 224) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386b8 M')
        /\ (forall x, In x KS_vaS2_1b_11 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ (((V 37%nat) - 237) mod 2 ^ 64) < 1
        /\ 1 <= (((V 37%nat) - 224) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386e0 M')
        /\ (forall x, In x KS_vaS2_1b_12 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ 1 <= (((V 37%nat) - 237) mod 2 ^ 64)
        /\ 1 <= (((V 37%nat) - 224) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386b8 M')
        /\ (forall x, In x KS_vaS2_1b_13 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ (V 37%nat) < 245
        /\ 1 <= (((V 37%nat) - 237) mod 2 ^ 64)
        /\ 1 <= (((V 37%nat) - 224) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386e0 M')
        /\ (forall x, In x KS_vaS2_1b_14 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ 245 <= (V 37%nat)
        /\ 1 <= (((V 37%nat) - 237) mod 2 ^ 64)
        /\ 1 <= (((V 37%nat) - 224) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G5 G6 G7 G8 G9 G10 G12 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G24 G25 G28 G29 G30 G31 pvzI6 pvzI7 pvzI8 K3 pvzI9 pvzI10.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K1l; move K1l before pvzI7; pose proof (proj2 pvzI7) as K1r; move K1r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K2l; move K2l before pvzI8; pose proof (proj2 pvzI8) as K2r; move K2r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K4l; move K4l before pvzI9; pose proof (proj2 pvzI9) as K4r; move K4r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K5l; move K5l before pvzI10; pose proof (proj2 pvzI10) as K5r; move K5r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_39 := V 39%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | 39%nat => Z_to_bv 64 vz_39 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 37%nat => vz_37 | 39%nat => vz_39 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 40%nat. }
  assert (HR: regs_ok E PvaS2_1b.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvaS2_1b.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvaS2_1b.kn0).
  { unfold know_ok, PvaS2_1b.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV39l HV39r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV39l HV39r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K5l K5r) | exact (conj K5l K5r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvaS2_1b.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvaS2_1b.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvaS2_1b.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PvaS2_1b.ps0) with 0x386e0 in Hms. change (SR.ps_regs PvaS2_1b.ps0) with (map (fun i => (i, nth i PvaS2_1b.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_1b.ps0) with PvaS2_1b.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_1b.regs0 PvaS2_1b.regs_out0 60 KS_vaS2_1b_0 KS_vaS2_1b_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PvaS2_1b.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. left.
    change (SR.ps_pc PvaS2_1b.ps1) with 0x386e0 in Hms. change (SR.ps_regs PvaS2_1b.ps1) with (map (fun i => (i, nth i PvaS2_1b.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_1b.ps1) with PvaS2_1b.cells1 in Hcells. unfold PvaS2_1b.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_1b.regs0 PvaS2_1b.regs_out1 60 KS_vaS2_1b_1 KS_vaS2_1b_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out1 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out1 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out1 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. left.
    change (SR.ps_pc PvaS2_1b.ps2) with 0x386b8 in Hms. change (SR.ps_regs PvaS2_1b.ps2) with (map (fun i => (i, nth i PvaS2_1b.regs_out2 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_1b.ps2) with PvaS2_1b.cells2 in Hcells. unfold PvaS2_1b.cells2 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_1b.regs0 PvaS2_1b.regs_out2 60 KS_vaS2_1b_2 KS_vaS2_1b_2_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out2 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out2 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out2 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. left.
    change (SR.ps_pc PvaS2_1b.ps3) with 0x386e0 in Hms. change (SR.ps_regs PvaS2_1b.ps3) with (map (fun i => (i, nth i PvaS2_1b.regs_out3 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_1b.ps3) with PvaS2_1b.cells3 in Hcells. unfold PvaS2_1b.cells3 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_1b.regs0 PvaS2_1b.regs_out3 60 KS_vaS2_1b_3 KS_vaS2_1b_3_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out3 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out3 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out3 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out3 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. left.
    change (SR.ps_pc PvaS2_1b.ps4) with 0x386b8 in Hms. change (SR.ps_regs PvaS2_1b.ps4) with (map (fun i => (i, nth i PvaS2_1b.regs_out4 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_1b.ps4) with PvaS2_1b.cells4 in Hcells. unfold PvaS2_1b.cells4 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_1b.regs0 PvaS2_1b.regs_out4 60 KS_vaS2_1b_4 KS_vaS2_1b_4_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out4 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out4 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out4 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. left.
    change (SR.ps_pc PvaS2_1b.ps5) with 0x386e0 in Hms. change (SR.ps_regs PvaS2_1b.ps5) with (map (fun i => (i, nth i PvaS2_1b.regs_out5 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_1b.ps5) with PvaS2_1b.cells5 in Hcells. unfold PvaS2_1b.cells5 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_1b.regs0 PvaS2_1b.regs_out5 60 KS_vaS2_1b_5 KS_vaS2_1b_5_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out5 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out5]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out5 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out5]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out5 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out5]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out5 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out5]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. left.
    change (SR.ps_pc PvaS2_1b.ps6) with 0x386b8 in Hms. change (SR.ps_regs PvaS2_1b.ps6) with (map (fun i => (i, nth i PvaS2_1b.regs_out6 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_1b.ps6) with PvaS2_1b.cells6 in Hcells. unfold PvaS2_1b.cells6 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_1b.regs0 PvaS2_1b.regs_out6 60 KS_vaS2_1b_6 KS_vaS2_1b_6_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out6 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out6 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out6 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out6 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. left.
    change (SR.ps_pc PvaS2_1b.ps7) with 0x386e0 in Hms. change (SR.ps_regs PvaS2_1b.ps7) with (map (fun i => (i, nth i PvaS2_1b.regs_out7 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_1b.ps7) with PvaS2_1b.cells7 in Hcells. unfold PvaS2_1b.cells7 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_1b.regs0 PvaS2_1b.regs_out7 60 KS_vaS2_1b_7 KS_vaS2_1b_7_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out7 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out7]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out7 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out7]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out7 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out7]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out7 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out7]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. right. left.
    change (SR.ps_pc PvaS2_1b.ps8) with 0x386e0 in Hms. change (SR.ps_regs PvaS2_1b.ps8) with (map (fun i => (i, nth i PvaS2_1b.regs_out8 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_1b.ps8) with PvaS2_1b.cells8 in Hcells. unfold PvaS2_1b.cells8 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_1b.regs0 PvaS2_1b.regs_out8 60 KS_vaS2_1b_8 KS_vaS2_1b_8_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out8 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out8]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out8 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out8]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out8 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out8]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out8 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out8]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. right. right. left.
    change (SR.ps_pc PvaS2_1b.ps9) with 0x386b8 in Hms. change (SR.ps_regs PvaS2_1b.ps9) with (map (fun i => (i, nth i PvaS2_1b.regs_out9 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_1b.ps9) with PvaS2_1b.cells9 in Hcells. unfold PvaS2_1b.cells9 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_1b.regs0 PvaS2_1b.regs_out9 60 KS_vaS2_1b_9 KS_vaS2_1b_9_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out9 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out9]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out9 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out9]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out9 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out9]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. right. right. right. left.
    change (SR.ps_pc PvaS2_1b.ps10) with 0x386e0 in Hms. change (SR.ps_regs PvaS2_1b.ps10) with (map (fun i => (i, nth i PvaS2_1b.regs_out10 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_1b.ps10) with PvaS2_1b.cells10 in Hcells. unfold PvaS2_1b.cells10 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_1b.regs0 PvaS2_1b.regs_out10 60 KS_vaS2_1b_10 KS_vaS2_1b_10_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out10 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out10]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out10 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out10]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out10 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out10]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out10 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out10]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. right. right. right. right. left.
    change (SR.ps_pc PvaS2_1b.ps11) with 0x386b8 in Hms. change (SR.ps_regs PvaS2_1b.ps11) with (map (fun i => (i, nth i PvaS2_1b.regs_out11 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_1b.ps11) with PvaS2_1b.cells11 in Hcells. unfold PvaS2_1b.cells11 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_1b.regs0 PvaS2_1b.regs_out11 60 KS_vaS2_1b_11 KS_vaS2_1b_11_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out11 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out11]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out11 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out11]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out11 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out11]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. right. right. right. right. right. left.
    change (SR.ps_pc PvaS2_1b.ps12) with 0x386e0 in Hms. change (SR.ps_regs PvaS2_1b.ps12) with (map (fun i => (i, nth i PvaS2_1b.regs_out12 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_1b.ps12) with PvaS2_1b.cells12 in Hcells. unfold PvaS2_1b.cells12 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_1b.regs0 PvaS2_1b.regs_out12 60 KS_vaS2_1b_12 KS_vaS2_1b_12_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out12 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out12]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out12 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out12]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out12 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out12]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out12 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out12]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. right. right. right. right. right. right. left.
    change (SR.ps_pc PvaS2_1b.ps13) with 0x386b8 in Hms. change (SR.ps_regs PvaS2_1b.ps13) with (map (fun i => (i, nth i PvaS2_1b.regs_out13 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_1b.ps13) with PvaS2_1b.cells13 in Hcells. unfold PvaS2_1b.cells13 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_1b.regs0 PvaS2_1b.regs_out13 60 KS_vaS2_1b_13 KS_vaS2_1b_13_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out13 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out13]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out13 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out13]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out13 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out13]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out13 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out13]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. right. right. right. right. right. right. right. 
    change (SR.ps_pc PvaS2_1b.ps14) with 0x386e0 in Hms. change (SR.ps_regs PvaS2_1b.ps14) with (map (fun i => (i, nth i PvaS2_1b.regs_out14 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_1b.ps14) with PvaS2_1b.cells14 in Hcells. unfold PvaS2_1b.cells14 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_1b.regs0 PvaS2_1b.regs_out14 60 KS_vaS2_1b_14 KS_vaS2_1b_14_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out14 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out14]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out14 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out14]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out14 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out14]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_1b.regs_out14 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_1b.regs_out14]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvaS2_2a := LibSegBs_vaS2_2a_u.
Definition KS_vaS2_2a : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_2a.regs0 PvaS2_2a.regs_out0).
Lemma KS_vaS2_2a_ok : BG.kept_ok 60 PvaS2_2a.regs0 PvaS2_2a.regs_out0 KS_vaS2_2a = true. Proof. vm_compute. reflexivity. Qed.
Lemma vaS2_2a_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 2 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 13) = Z_to_bv 64 8 -> getr R (reg 14) = Z_to_bv 64 (-1) -> getr R (reg 15) = Z_to_bv 64 1 -> getr R (reg 16) = Z_to_bv 64 (-62) -> getr R (reg 17) = Z_to_bv 64 245 -> getr R (reg 18) = Z_to_bv 64 244 -> getr R (reg 19) = Z_to_bv 64 143 -> getr R (reg 20) = Z_to_bv 64 80240 -> getr R (reg 21) = Z_to_bv 64 (-80241) -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 24) = Z_to_bv 64 (V 37%nat) -> getr R (reg 25) = Z_to_bv 64 2 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 2 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386e0 M')
        /\ (forall x, In x KS_vaS2_2a -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 5).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G12 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G24 G25 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 pvzI8.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PvaS2_2a.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvaS2_2a.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvaS2_2a.kn0).
  { unfold know_ok, PvaS2_2a.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvaS2_2a.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvaS2_2a.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvaS2_2a.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvaS2_2a.ps0) with 0x386e0 in Hms. change (SR.ps_regs PvaS2_2a.ps0) with (map (fun i => (i, nth i PvaS2_2a.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvaS2_2a.ps0) with PvaS2_2a.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_2a.regs0 PvaS2_2a.regs_out0 60 KS_vaS2_2a KS_vaS2_2a_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg PvaS2_2a.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaS2_2a.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvaS2_2b := LibSegBs_vaS2_2b_u.
Definition KS_vaS2_2b_0 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_2b.regs0 PvaS2_2b.regs_out0).
Lemma KS_vaS2_2b_0_ok : BG.kept_ok 60 PvaS2_2b.regs0 PvaS2_2b.regs_out0 KS_vaS2_2b_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_2b_1 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_2b.regs0 PvaS2_2b.regs_out1).
Lemma KS_vaS2_2b_1_ok : BG.kept_ok 60 PvaS2_2b.regs0 PvaS2_2b.regs_out1 KS_vaS2_2b_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_2b_2 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_2b.regs0 PvaS2_2b.regs_out2).
Lemma KS_vaS2_2b_2_ok : BG.kept_ok 60 PvaS2_2b.regs0 PvaS2_2b.regs_out2 KS_vaS2_2b_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_2b_3 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_2b.regs0 PvaS2_2b.regs_out3).
Lemma KS_vaS2_2b_3_ok : BG.kept_ok 60 PvaS2_2b.regs0 PvaS2_2b.regs_out3 KS_vaS2_2b_3 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_2b_4 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_2b.regs0 PvaS2_2b.regs_out4).
Lemma KS_vaS2_2b_4_ok : BG.kept_ok 60 PvaS2_2b.regs0 PvaS2_2b.regs_out4 KS_vaS2_2b_4 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_2b_5 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_2b.regs0 PvaS2_2b.regs_out5).
Lemma KS_vaS2_2b_5_ok : BG.kept_ok 60 PvaS2_2b.regs0 PvaS2_2b.regs_out5 KS_vaS2_2b_5 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_2b_6 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_2b.regs0 PvaS2_2b.regs_out6).
Lemma KS_vaS2_2b_6_ok : BG.kept_ok 60 PvaS2_2b.regs0 PvaS2_2b.regs_out6 KS_vaS2_2b_6 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_2b_7 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_2b.regs0 PvaS2_2b.regs_out7).
Lemma KS_vaS2_2b_7_ok : BG.kept_ok 60 PvaS2_2b.regs0 PvaS2_2b.regs_out7 KS_vaS2_2b_7 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_2b_8 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_2b.regs0 PvaS2_2b.regs_out8).
Lemma KS_vaS2_2b_8_ok : BG.kept_ok 60 PvaS2_2b.regs0 PvaS2_2b.regs_out8 KS_vaS2_2b_8 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_2b_9 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_2b.regs0 PvaS2_2b.regs_out9).
Lemma KS_vaS2_2b_9_ok : BG.kept_ok 60 PvaS2_2b.regs0 PvaS2_2b.regs_out9 KS_vaS2_2b_9 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_2b_10 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_2b.regs0 PvaS2_2b.regs_out10).
Lemma KS_vaS2_2b_10_ok : BG.kept_ok 60 PvaS2_2b.regs0 PvaS2_2b.regs_out10 KS_vaS2_2b_10 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_2b_11 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_2b.regs0 PvaS2_2b.regs_out11).
Lemma KS_vaS2_2b_11_ok : BG.kept_ok 60 PvaS2_2b.regs0 PvaS2_2b.regs_out11 KS_vaS2_2b_11 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_2b_12 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_2b.regs0 PvaS2_2b.regs_out12).
Lemma KS_vaS2_2b_12_ok : BG.kept_ok 60 PvaS2_2b.regs0 PvaS2_2b.regs_out12 KS_vaS2_2b_12 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_2b_13 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_2b.regs0 PvaS2_2b.regs_out13).
Lemma KS_vaS2_2b_13_ok : BG.kept_ok 60 PvaS2_2b.regs0 PvaS2_2b.regs_out13 KS_vaS2_2b_13 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_2b_14 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_2b.regs0 PvaS2_2b.regs_out14).
Lemma KS_vaS2_2b_14_ok : BG.kept_ok 60 PvaS2_2b.regs0 PvaS2_2b.regs_out14 KS_vaS2_2b_14 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_2b_15 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_2b.regs0 PvaS2_2b.regs_out15).
Lemma KS_vaS2_2b_15_ok : BG.kept_ok 60 PvaS2_2b.regs0 PvaS2_2b.regs_out15 KS_vaS2_2b_15 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vaS2_2b_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 2 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 13) = Z_to_bv 64 8 -> getr R (reg 14) = Z_to_bv 64 (-1) -> getr R (reg 15) = Z_to_bv 64 1 -> getr R (reg 16) = Z_to_bv 64 (-62) -> getr R (reg 17) = Z_to_bv 64 245 -> getr R (reg 18) = Z_to_bv 64 244 -> getr R (reg 19) = Z_to_bv 64 143 -> getr R (reg 20) = Z_to_bv 64 80240 -> getr R (reg 21) = Z_to_bv 64 (-80241) -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 24) = Z_to_bv 64 (V 37%nat) -> getr R (reg 25) = Z_to_bv 64 2 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 3 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 1) (V 39%nat) ->
  0 <= (V 39%nat) <= 255 -> L5.u8_at RSEGS M ((V 33%nat) + 2) (V 40%nat) -> 0 <= (V 40%nat) <= 255 -> 0 <= (V 37%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386e0 M')
        /\ (forall x, In x KS_vaS2_2b_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 3))
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386e0 M')
        /\ (forall x, In x KS_vaS2_2b_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 2))
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386e0 M')
        /\ (forall x, In x KS_vaS2_2b_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ (((V 37%nat) - 240) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386b8 M')
        /\ (forall x, In x KS_vaS2_2b_3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ (((V 37%nat) - 240) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386e0 M')
        /\ (forall x, In x KS_vaS2_2b_4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ (((V 37%nat) - 244) mod 2 ^ 64) < 1
        /\ 1 <= (((V 37%nat) - 240) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386b8 M')
        /\ (forall x, In x KS_vaS2_2b_5 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ (((V 37%nat) - 244) mod 2 ^ 64) < 1
        /\ 1 <= (((V 37%nat) - 240) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386e0 M')
        /\ (forall x, In x KS_vaS2_2b_6 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ 1 <= (((V 37%nat) - 244) mod 2 ^ 64)
        /\ 1 <= (((V 37%nat) - 240) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386b8 M')
        /\ (forall x, In x KS_vaS2_2b_7 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ (V 37%nat) < 245
        /\ 1 <= (((V 37%nat) - 244) mod 2 ^ 64)
        /\ 1 <= (((V 37%nat) - 240) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386e0 M')
        /\ (forall x, In x KS_vaS2_2b_8 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ 245 <= (V 37%nat)
        /\ 1 <= (((V 37%nat) - 244) mod 2 ^ 64)
        /\ 1 <= (((V 37%nat) - 240) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386e0 M')
        /\ (forall x, In x KS_vaS2_2b_9 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ (((V 37%nat) - 224) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386b8 M')
        /\ (forall x, In x KS_vaS2_2b_10 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ (((V 37%nat) - 224) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386e0 M')
        /\ (forall x, In x KS_vaS2_2b_11 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ (((V 37%nat) - 237) mod 2 ^ 64) < 1
        /\ 1 <= (((V 37%nat) - 224) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386b8 M')
        /\ (forall x, In x KS_vaS2_2b_12 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ (((V 37%nat) - 237) mod 2 ^ 64) < 1
        /\ 1 <= (((V 37%nat) - 224) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386e0 M')
        /\ (forall x, In x KS_vaS2_2b_13 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ 1 <= (((V 37%nat) - 237) mod 2 ^ 64)
        /\ 1 <= (((V 37%nat) - 224) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386b8 M')
        /\ (forall x, In x KS_vaS2_2b_14 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ (V 37%nat) < 245
        /\ 1 <= (((V 37%nat) - 237) mod 2 ^ 64)
        /\ 1 <= (((V 37%nat) - 224) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386e0 M')
        /\ (forall x, In x KS_vaS2_2b_15 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ 245 <= (V 37%nat)
        /\ 1 <= (((V 37%nat) - 237) mod 2 ^ 64)
        /\ 1 <= (((V 37%nat) - 224) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G5 G6 G7 G8 G9 G10 G12 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G24 G25 G28 G29 G30 G31 pvzI7 pvzI8 pvzI9 K3 pvzI10 K5 pvzI11 pvzI12.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV40l; move HV40l before pvzI6; pose proof (proj2 pvzI6) as HV40r; move HV40r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K1l; move K1l before pvzI8; pose proof (proj2 pvzI8) as K1r; move K1r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K2l; move K2l before pvzI9; pose proof (proj2 pvzI9) as K2r; move K2r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K4l; move K4l before pvzI10; pose proof (proj2 pvzI10) as K4r; move K4r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K6l; move K6l before pvzI11; pose proof (proj2 pvzI11) as K6r; move K6r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K7l; move K7l before pvzI12; pose proof (proj2 pvzI12) as K7r; move K7r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 37%nat => vz_37 | 39%nat => vz_39 | 40%nat => vz_40 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 41%nat. }
  assert (HR: regs_ok E PvaS2_2b.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvaS2_2b.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvaS2_2b.kn0).
  { unfold know_ok, PvaS2_2b.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV39l HV39r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV39l HV39r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV40l HV40r K6l K6r) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvaS2_2b.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvaS2_2b.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvaS2_2b.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PvaS2_2b.ps0) with 0x386e0 in Hms. change (SR.ps_regs PvaS2_2b.ps0) with (map (fun i => (i, nth i PvaS2_2b.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_2b.ps0) with PvaS2_2b.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_2b.regs0 PvaS2_2b.regs_out0 60 KS_vaS2_2b_0 KS_vaS2_2b_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PvaS2_2b.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. left.
    change (SR.ps_pc PvaS2_2b.ps1) with 0x386e0 in Hms. change (SR.ps_regs PvaS2_2b.ps1) with (map (fun i => (i, nth i PvaS2_2b.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_2b.ps1) with PvaS2_2b.cells1 in Hcells. unfold PvaS2_2b.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_2b.regs0 PvaS2_2b.regs_out1 60 KS_vaS2_2b_1 KS_vaS2_2b_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out1 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out1 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PvaS2_2b.regs_out1 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out1]. first [reflexivity | wordP' ZA Hag]. 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. left.
    change (SR.ps_pc PvaS2_2b.ps2) with 0x386e0 in Hms. change (SR.ps_regs PvaS2_2b.ps2) with (map (fun i => (i, nth i PvaS2_2b.regs_out2 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_2b.ps2) with PvaS2_2b.cells2 in Hcells. unfold PvaS2_2b.cells2 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_2b.regs0 PvaS2_2b.regs_out2 60 KS_vaS2_2b_2 KS_vaS2_2b_2_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out2 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out2 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out2 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out2 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. left.
    change (SR.ps_pc PvaS2_2b.ps3) with 0x386b8 in Hms. change (SR.ps_regs PvaS2_2b.ps3) with (map (fun i => (i, nth i PvaS2_2b.regs_out3 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_2b.ps3) with PvaS2_2b.cells3 in Hcells. unfold PvaS2_2b.cells3 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_2b.regs0 PvaS2_2b.regs_out3 60 KS_vaS2_2b_3 KS_vaS2_2b_3_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out3 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out3 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out3 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. left.
    change (SR.ps_pc PvaS2_2b.ps4) with 0x386e0 in Hms. change (SR.ps_regs PvaS2_2b.ps4) with (map (fun i => (i, nth i PvaS2_2b.regs_out4 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_2b.ps4) with PvaS2_2b.cells4 in Hcells. unfold PvaS2_2b.cells4 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_2b.regs0 PvaS2_2b.regs_out4 60 KS_vaS2_2b_4 KS_vaS2_2b_4_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out4 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out4 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out4 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out4 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. left.
    change (SR.ps_pc PvaS2_2b.ps5) with 0x386b8 in Hms. change (SR.ps_regs PvaS2_2b.ps5) with (map (fun i => (i, nth i PvaS2_2b.regs_out5 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_2b.ps5) with PvaS2_2b.cells5 in Hcells. unfold PvaS2_2b.cells5 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_2b.regs0 PvaS2_2b.regs_out5 60 KS_vaS2_2b_5 KS_vaS2_2b_5_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out5 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out5]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out5 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out5]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out5 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out5]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. left.
    change (SR.ps_pc PvaS2_2b.ps6) with 0x386e0 in Hms. change (SR.ps_regs PvaS2_2b.ps6) with (map (fun i => (i, nth i PvaS2_2b.regs_out6 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_2b.ps6) with PvaS2_2b.cells6 in Hcells. unfold PvaS2_2b.cells6 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_2b.regs0 PvaS2_2b.regs_out6 60 KS_vaS2_2b_6 KS_vaS2_2b_6_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out6 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out6 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out6 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out6 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. left.
    change (SR.ps_pc PvaS2_2b.ps7) with 0x386b8 in Hms. change (SR.ps_regs PvaS2_2b.ps7) with (map (fun i => (i, nth i PvaS2_2b.regs_out7 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_2b.ps7) with PvaS2_2b.cells7 in Hcells. unfold PvaS2_2b.cells7 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_2b.regs0 PvaS2_2b.regs_out7 60 KS_vaS2_2b_7 KS_vaS2_2b_7_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out7 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out7]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out7 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out7]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out7 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out7]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out7 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out7]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. right. left.
    change (SR.ps_pc PvaS2_2b.ps8) with 0x386e0 in Hms. change (SR.ps_regs PvaS2_2b.ps8) with (map (fun i => (i, nth i PvaS2_2b.regs_out8 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_2b.ps8) with PvaS2_2b.cells8 in Hcells. unfold PvaS2_2b.cells8 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_2b.regs0 PvaS2_2b.regs_out8 60 KS_vaS2_2b_8 KS_vaS2_2b_8_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out8 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out8]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out8 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out8]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out8 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out8]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out8 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out8]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. right. right. left.
    change (SR.ps_pc PvaS2_2b.ps9) with 0x386e0 in Hms. change (SR.ps_regs PvaS2_2b.ps9) with (map (fun i => (i, nth i PvaS2_2b.regs_out9 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_2b.ps9) with PvaS2_2b.cells9 in Hcells. unfold PvaS2_2b.cells9 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_2b.regs0 PvaS2_2b.regs_out9 60 KS_vaS2_2b_9 KS_vaS2_2b_9_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out9 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out9]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out9 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out9]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out9 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out9]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out9 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out9]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. right. right. right. left.
    change (SR.ps_pc PvaS2_2b.ps10) with 0x386b8 in Hms. change (SR.ps_regs PvaS2_2b.ps10) with (map (fun i => (i, nth i PvaS2_2b.regs_out10 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_2b.ps10) with PvaS2_2b.cells10 in Hcells. unfold PvaS2_2b.cells10 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_2b.regs0 PvaS2_2b.regs_out10 60 KS_vaS2_2b_10 KS_vaS2_2b_10_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out10 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out10]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out10 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out10]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out10 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out10]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. right. right. right. right. left.
    change (SR.ps_pc PvaS2_2b.ps11) with 0x386e0 in Hms. change (SR.ps_regs PvaS2_2b.ps11) with (map (fun i => (i, nth i PvaS2_2b.regs_out11 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_2b.ps11) with PvaS2_2b.cells11 in Hcells. unfold PvaS2_2b.cells11 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_2b.regs0 PvaS2_2b.regs_out11 60 KS_vaS2_2b_11 KS_vaS2_2b_11_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out11 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out11]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out11 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out11]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out11 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out11]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out11 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out11]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. right. right. right. right. right. left.
    change (SR.ps_pc PvaS2_2b.ps12) with 0x386b8 in Hms. change (SR.ps_regs PvaS2_2b.ps12) with (map (fun i => (i, nth i PvaS2_2b.regs_out12 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_2b.ps12) with PvaS2_2b.cells12 in Hcells. unfold PvaS2_2b.cells12 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_2b.regs0 PvaS2_2b.regs_out12 60 KS_vaS2_2b_12 KS_vaS2_2b_12_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out12 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out12]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out12 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out12]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out12 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out12]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. right. right. right. right. right. right. left.
    change (SR.ps_pc PvaS2_2b.ps13) with 0x386e0 in Hms. change (SR.ps_regs PvaS2_2b.ps13) with (map (fun i => (i, nth i PvaS2_2b.regs_out13 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_2b.ps13) with PvaS2_2b.cells13 in Hcells. unfold PvaS2_2b.cells13 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_2b.regs0 PvaS2_2b.regs_out13 60 KS_vaS2_2b_13 KS_vaS2_2b_13_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out13 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out13]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out13 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out13]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out13 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out13]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out13 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out13]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. right. right. right. right. right. right. right. left.
    change (SR.ps_pc PvaS2_2b.ps14) with 0x386b8 in Hms. change (SR.ps_regs PvaS2_2b.ps14) with (map (fun i => (i, nth i PvaS2_2b.regs_out14 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_2b.ps14) with PvaS2_2b.cells14 in Hcells. unfold PvaS2_2b.cells14 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_2b.regs0 PvaS2_2b.regs_out14 60 KS_vaS2_2b_14 KS_vaS2_2b_14_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out14 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out14]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out14 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out14]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out14 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out14]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out14 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out14]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. right. right. right. right. right. right. right. right. 
    change (SR.ps_pc PvaS2_2b.ps15) with 0x386e0 in Hms. change (SR.ps_regs PvaS2_2b.ps15) with (map (fun i => (i, nth i PvaS2_2b.regs_out15 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_2b.ps15) with PvaS2_2b.cells15 in Hcells. unfold PvaS2_2b.cells15 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_2b.regs0 PvaS2_2b.regs_out15 60 KS_vaS2_2b_15 KS_vaS2_2b_15_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out15 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out15]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out15 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out15]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out15 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out15]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_2b.regs_out15 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_2b.regs_out15]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvaS2_3a := LibSegBs_vaS2_3a_u.
Definition KS_vaS2_3a : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_3a.regs0 PvaS2_3a.regs_out0).
Lemma KS_vaS2_3a_ok : BG.kept_ok 60 PvaS2_3a.regs0 PvaS2_3a.regs_out0 KS_vaS2_3a = true. Proof. vm_compute. reflexivity. Qed.
Lemma vaS2_3a_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 2 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 13) = Z_to_bv 64 8 -> getr R (reg 14) = Z_to_bv 64 (-1) -> getr R (reg 15) = Z_to_bv 64 1 -> getr R (reg 16) = Z_to_bv 64 (-62) -> getr R (reg 17) = Z_to_bv 64 245 -> getr R (reg 18) = Z_to_bv 64 244 -> getr R (reg 19) = Z_to_bv 64 143 -> getr R (reg 20) = Z_to_bv 64 80240 -> getr R (reg 21) = Z_to_bv 64 (-80241) -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 24) = Z_to_bv 64 (V 37%nat) -> getr R (reg 25) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 3 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386e0 M')
        /\ (forall x, In x KS_vaS2_3a -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 5).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G12 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G24 G25 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 pvzI8.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PvaS2_3a.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvaS2_3a.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvaS2_3a.kn0).
  { unfold know_ok, PvaS2_3a.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvaS2_3a.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvaS2_3a.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvaS2_3a.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvaS2_3a.ps0) with 0x386e0 in Hms. change (SR.ps_regs PvaS2_3a.ps0) with (map (fun i => (i, nth i PvaS2_3a.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvaS2_3a.ps0) with PvaS2_3a.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_3a.regs0 PvaS2_3a.regs_out0 60 KS_vaS2_3a KS_vaS2_3a_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg PvaS2_3a.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaS2_3a.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvaS2_3b := LibSegBs_vaS2_3b_u.
Definition KS_vaS2_3b_0 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_3b.regs0 PvaS2_3b.regs_out0).
Lemma KS_vaS2_3b_0_ok : BG.kept_ok 60 PvaS2_3b.regs0 PvaS2_3b.regs_out0 KS_vaS2_3b_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_3b_1 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_3b.regs0 PvaS2_3b.regs_out1).
Lemma KS_vaS2_3b_1_ok : BG.kept_ok 60 PvaS2_3b.regs0 PvaS2_3b.regs_out1 KS_vaS2_3b_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_3b_2 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_3b.regs0 PvaS2_3b.regs_out2).
Lemma KS_vaS2_3b_2_ok : BG.kept_ok 60 PvaS2_3b.regs0 PvaS2_3b.regs_out2 KS_vaS2_3b_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_3b_3 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_3b.regs0 PvaS2_3b.regs_out3).
Lemma KS_vaS2_3b_3_ok : BG.kept_ok 60 PvaS2_3b.regs0 PvaS2_3b.regs_out3 KS_vaS2_3b_3 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_3b_4 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_3b.regs0 PvaS2_3b.regs_out4).
Lemma KS_vaS2_3b_4_ok : BG.kept_ok 60 PvaS2_3b.regs0 PvaS2_3b.regs_out4 KS_vaS2_3b_4 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_3b_5 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_3b.regs0 PvaS2_3b.regs_out5).
Lemma KS_vaS2_3b_5_ok : BG.kept_ok 60 PvaS2_3b.regs0 PvaS2_3b.regs_out5 KS_vaS2_3b_5 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_3b_6 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_3b.regs0 PvaS2_3b.regs_out6).
Lemma KS_vaS2_3b_6_ok : BG.kept_ok 60 PvaS2_3b.regs0 PvaS2_3b.regs_out6 KS_vaS2_3b_6 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_3b_7 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_3b.regs0 PvaS2_3b.regs_out7).
Lemma KS_vaS2_3b_7_ok : BG.kept_ok 60 PvaS2_3b.regs0 PvaS2_3b.regs_out7 KS_vaS2_3b_7 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_3b_8 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_3b.regs0 PvaS2_3b.regs_out8).
Lemma KS_vaS2_3b_8_ok : BG.kept_ok 60 PvaS2_3b.regs0 PvaS2_3b.regs_out8 KS_vaS2_3b_8 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_3b_9 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_3b.regs0 PvaS2_3b.regs_out9).
Lemma KS_vaS2_3b_9_ok : BG.kept_ok 60 PvaS2_3b.regs0 PvaS2_3b.regs_out9 KS_vaS2_3b_9 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_3b_10 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_3b.regs0 PvaS2_3b.regs_out10).
Lemma KS_vaS2_3b_10_ok : BG.kept_ok 60 PvaS2_3b.regs0 PvaS2_3b.regs_out10 KS_vaS2_3b_10 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_3b_11 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_3b.regs0 PvaS2_3b.regs_out11).
Lemma KS_vaS2_3b_11_ok : BG.kept_ok 60 PvaS2_3b.regs0 PvaS2_3b.regs_out11 KS_vaS2_3b_11 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_3b_12 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_3b.regs0 PvaS2_3b.regs_out12).
Lemma KS_vaS2_3b_12_ok : BG.kept_ok 60 PvaS2_3b.regs0 PvaS2_3b.regs_out12 KS_vaS2_3b_12 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_3b_13 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_3b.regs0 PvaS2_3b.regs_out13).
Lemma KS_vaS2_3b_13_ok : BG.kept_ok 60 PvaS2_3b.regs0 PvaS2_3b.regs_out13 KS_vaS2_3b_13 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_3b_14 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_3b.regs0 PvaS2_3b.regs_out14).
Lemma KS_vaS2_3b_14_ok : BG.kept_ok 60 PvaS2_3b.regs0 PvaS2_3b.regs_out14 KS_vaS2_3b_14 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_3b_15 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_3b.regs0 PvaS2_3b.regs_out15).
Lemma KS_vaS2_3b_15_ok : BG.kept_ok 60 PvaS2_3b.regs0 PvaS2_3b.regs_out15 KS_vaS2_3b_15 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_3b_16 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_3b.regs0 PvaS2_3b.regs_out16).
Lemma KS_vaS2_3b_16_ok : BG.kept_ok 60 PvaS2_3b.regs0 PvaS2_3b.regs_out16 KS_vaS2_3b_16 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vaS2_3b_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 2 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 13) = Z_to_bv 64 8 -> getr R (reg 14) = Z_to_bv 64 (-1) -> getr R (reg 15) = Z_to_bv 64 1 -> getr R (reg 16) = Z_to_bv 64 (-62) -> getr R (reg 17) = Z_to_bv 64 245 -> getr R (reg 18) = Z_to_bv 64 244 -> getr R (reg 19) = Z_to_bv 64 143 -> getr R (reg 20) = Z_to_bv 64 80240 -> getr R (reg 21) = Z_to_bv 64 (-80241) -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 24) = Z_to_bv 64 (V 37%nat) -> getr R (reg 25) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 4 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 1) (V 39%nat) ->
  0 <= (V 39%nat) <= 255 -> L5.u8_at RSEGS M ((V 33%nat) + 2) (V 40%nat) -> 0 <= (V 40%nat) <= 255 -> L5.u8_at RSEGS M ((V 33%nat) + 3) (V 41%nat) ->
  0 <= (V 41%nat) <= 255 -> 0 <= (V 37%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386e0 M')
        /\ (forall x, In x KS_vaS2_3b_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 4)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 3))
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386e0 M')
        /\ (forall x, In x KS_vaS2_3b_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 4)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 3))
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386e0 M')
        /\ (forall x, In x KS_vaS2_3b_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 4)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 2))
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386e0 M')
        /\ (forall x, In x KS_vaS2_3b_3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 4)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ (((V 37%nat) - 240) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386b8 M')
        /\ (forall x, In x KS_vaS2_3b_4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 4)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ (((V 37%nat) - 240) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386e0 M')
        /\ (forall x, In x KS_vaS2_3b_5 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 4)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ (((V 37%nat) - 244) mod 2 ^ 64) < 1
        /\ 1 <= (((V 37%nat) - 240) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386b8 M')
        /\ (forall x, In x KS_vaS2_3b_6 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 4)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ (((V 37%nat) - 244) mod 2 ^ 64) < 1
        /\ 1 <= (((V 37%nat) - 240) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386e0 M')
        /\ (forall x, In x KS_vaS2_3b_7 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 4)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ 1 <= (((V 37%nat) - 244) mod 2 ^ 64)
        /\ 1 <= (((V 37%nat) - 240) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386b8 M')
        /\ (forall x, In x KS_vaS2_3b_8 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 4)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ (V 37%nat) < 245
        /\ 1 <= (((V 37%nat) - 244) mod 2 ^ 64)
        /\ 1 <= (((V 37%nat) - 240) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386e0 M')
        /\ (forall x, In x KS_vaS2_3b_9 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 4)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ 245 <= (V 37%nat)
        /\ 1 <= (((V 37%nat) - 244) mod 2 ^ 64)
        /\ 1 <= (((V 37%nat) - 240) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386e0 M')
        /\ (forall x, In x KS_vaS2_3b_10 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 4)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ (((V 37%nat) - 224) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386b8 M')
        /\ (forall x, In x KS_vaS2_3b_11 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 4)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ (((V 37%nat) - 224) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386e0 M')
        /\ (forall x, In x KS_vaS2_3b_12 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 4)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ (((V 37%nat) - 237) mod 2 ^ 64) < 1
        /\ 1 <= (((V 37%nat) - 224) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386b8 M')
        /\ (forall x, In x KS_vaS2_3b_13 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 4)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ (((V 37%nat) - 237) mod 2 ^ 64) < 1
        /\ 1 <= (((V 37%nat) - 224) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386e0 M')
        /\ (forall x, In x KS_vaS2_3b_14 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 4)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ 1 <= (((V 37%nat) - 237) mod 2 ^ 64)
        /\ 1 <= (((V 37%nat) - 224) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386b8 M')
        /\ (forall x, In x KS_vaS2_3b_15 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 4)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ (V 37%nat) < 245
        /\ 1 <= (((V 37%nat) - 237) mod 2 ^ 64)
        /\ 1 <= (((V 37%nat) - 224) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386e0 M')
        /\ (forall x, In x KS_vaS2_3b_16 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 4)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ 245 <= (V 37%nat)
        /\ 1 <= (((V 37%nat) - 237) mod 2 ^ 64)
        /\ 1 <= (((V 37%nat) - 224) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G5 G6 G7 G8 G9 G10 G12 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G24 G25 G28 G29 G30 G31 pvzI8 pvzI9 pvzI10 K3 pvzI11 K5 pvzI12 K7 pvzI13 pvzI14.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV40l; move HV40l before pvzI6; pose proof (proj2 pvzI6) as HV40r; move HV40r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV41l; move HV41l before pvzI7; pose proof (proj2 pvzI7) as HV41r; move HV41r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K1l; move K1l before pvzI9; pose proof (proj2 pvzI9) as K1r; move K1r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K2l; move K2l before pvzI10; pose proof (proj2 pvzI10) as K2r; move K2r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K4l; move K4l before pvzI11; pose proof (proj2 pvzI11) as K4r; move K4r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K6l; move K6l before pvzI12; pose proof (proj2 pvzI12) as K6r; move K6r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K8l; move K8l before pvzI13; pose proof (proj2 pvzI13) as K8r; move K8r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K9l; move K9l before pvzI14; pose proof (proj2 pvzI14) as K9r; move K9r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 37%nat => vz_37 | 39%nat => vz_39 | 40%nat => vz_40 | 41%nat => vz_41 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E PvaS2_3b.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvaS2_3b.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvaS2_3b.kn0).
  { unfold know_ok, PvaS2_3b.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV39l HV39r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV39l HV39r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV40l HV40r K6l K6r) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV41l HV41r K8l K8r) | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvaS2_3b.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvaS2_3b.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvaS2_3b.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PvaS2_3b.ps0) with 0x386e0 in Hms. change (SR.ps_regs PvaS2_3b.ps0) with (map (fun i => (i, nth i PvaS2_3b.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_3b.ps0) with PvaS2_3b.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_3b.regs0 PvaS2_3b.regs_out0 60 KS_vaS2_3b_0 KS_vaS2_3b_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PvaS2_3b.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. left.
    change (SR.ps_pc PvaS2_3b.ps1) with 0x386e0 in Hms. change (SR.ps_regs PvaS2_3b.ps1) with (map (fun i => (i, nth i PvaS2_3b.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_3b.ps1) with PvaS2_3b.cells1 in Hcells. unfold PvaS2_3b.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_3b.regs0 PvaS2_3b.regs_out1 60 KS_vaS2_3b_1 KS_vaS2_3b_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out1 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out1 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PvaS2_3b.regs_out1 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out1]. first [reflexivity | wordP' ZA Hag]. 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. left.
    change (SR.ps_pc PvaS2_3b.ps2) with 0x386e0 in Hms. change (SR.ps_regs PvaS2_3b.ps2) with (map (fun i => (i, nth i PvaS2_3b.regs_out2 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_3b.ps2) with PvaS2_3b.cells2 in Hcells. unfold PvaS2_3b.cells2 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_3b.regs0 PvaS2_3b.regs_out2 60 KS_vaS2_3b_2 KS_vaS2_3b_2_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out2 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out2 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out2 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PvaS2_3b.regs_out2 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out2]. first [reflexivity | wordP' ZA Hag]. 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. left.
    change (SR.ps_pc PvaS2_3b.ps3) with 0x386e0 in Hms. change (SR.ps_regs PvaS2_3b.ps3) with (map (fun i => (i, nth i PvaS2_3b.regs_out3 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_3b.ps3) with PvaS2_3b.cells3 in Hcells. unfold PvaS2_3b.cells3 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_3b.regs0 PvaS2_3b.regs_out3 60 KS_vaS2_3b_3 KS_vaS2_3b_3_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out3 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out3 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out3 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out3 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. left.
    change (SR.ps_pc PvaS2_3b.ps4) with 0x386b8 in Hms. change (SR.ps_regs PvaS2_3b.ps4) with (map (fun i => (i, nth i PvaS2_3b.regs_out4 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_3b.ps4) with PvaS2_3b.cells4 in Hcells. unfold PvaS2_3b.cells4 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_3b.regs0 PvaS2_3b.regs_out4 60 KS_vaS2_3b_4 KS_vaS2_3b_4_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out4 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out4 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out4 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. left.
    change (SR.ps_pc PvaS2_3b.ps5) with 0x386e0 in Hms. change (SR.ps_regs PvaS2_3b.ps5) with (map (fun i => (i, nth i PvaS2_3b.regs_out5 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_3b.ps5) with PvaS2_3b.cells5 in Hcells. unfold PvaS2_3b.cells5 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_3b.regs0 PvaS2_3b.regs_out5 60 KS_vaS2_3b_5 KS_vaS2_3b_5_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out5 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out5]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out5 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out5]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out5 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out5]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out5 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out5]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. left.
    change (SR.ps_pc PvaS2_3b.ps6) with 0x386b8 in Hms. change (SR.ps_regs PvaS2_3b.ps6) with (map (fun i => (i, nth i PvaS2_3b.regs_out6 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_3b.ps6) with PvaS2_3b.cells6 in Hcells. unfold PvaS2_3b.cells6 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_3b.regs0 PvaS2_3b.regs_out6 60 KS_vaS2_3b_6 KS_vaS2_3b_6_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out6 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out6 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out6 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. left.
    change (SR.ps_pc PvaS2_3b.ps7) with 0x386e0 in Hms. change (SR.ps_regs PvaS2_3b.ps7) with (map (fun i => (i, nth i PvaS2_3b.regs_out7 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_3b.ps7) with PvaS2_3b.cells7 in Hcells. unfold PvaS2_3b.cells7 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_3b.regs0 PvaS2_3b.regs_out7 60 KS_vaS2_3b_7 KS_vaS2_3b_7_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out7 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out7]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out7 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out7]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out7 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out7]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out7 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out7]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. right. left.
    change (SR.ps_pc PvaS2_3b.ps8) with 0x386b8 in Hms. change (SR.ps_regs PvaS2_3b.ps8) with (map (fun i => (i, nth i PvaS2_3b.regs_out8 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_3b.ps8) with PvaS2_3b.cells8 in Hcells. unfold PvaS2_3b.cells8 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_3b.regs0 PvaS2_3b.regs_out8 60 KS_vaS2_3b_8 KS_vaS2_3b_8_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out8 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out8]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out8 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out8]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out8 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out8]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out8 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out8]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. right. right. left.
    change (SR.ps_pc PvaS2_3b.ps9) with 0x386e0 in Hms. change (SR.ps_regs PvaS2_3b.ps9) with (map (fun i => (i, nth i PvaS2_3b.regs_out9 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_3b.ps9) with PvaS2_3b.cells9 in Hcells. unfold PvaS2_3b.cells9 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_3b.regs0 PvaS2_3b.regs_out9 60 KS_vaS2_3b_9 KS_vaS2_3b_9_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out9 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out9]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out9 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out9]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out9 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out9]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out9 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out9]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. right. right. right. left.
    change (SR.ps_pc PvaS2_3b.ps10) with 0x386e0 in Hms. change (SR.ps_regs PvaS2_3b.ps10) with (map (fun i => (i, nth i PvaS2_3b.regs_out10 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_3b.ps10) with PvaS2_3b.cells10 in Hcells. unfold PvaS2_3b.cells10 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_3b.regs0 PvaS2_3b.regs_out10 60 KS_vaS2_3b_10 KS_vaS2_3b_10_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out10 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out10]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out10 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out10]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out10 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out10]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out10 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out10]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. right. right. right. right. left.
    change (SR.ps_pc PvaS2_3b.ps11) with 0x386b8 in Hms. change (SR.ps_regs PvaS2_3b.ps11) with (map (fun i => (i, nth i PvaS2_3b.regs_out11 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_3b.ps11) with PvaS2_3b.cells11 in Hcells. unfold PvaS2_3b.cells11 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_3b.regs0 PvaS2_3b.regs_out11 60 KS_vaS2_3b_11 KS_vaS2_3b_11_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out11 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out11]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out11 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out11]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out11 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out11]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. right. right. right. right. right. left.
    change (SR.ps_pc PvaS2_3b.ps12) with 0x386e0 in Hms. change (SR.ps_regs PvaS2_3b.ps12) with (map (fun i => (i, nth i PvaS2_3b.regs_out12 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_3b.ps12) with PvaS2_3b.cells12 in Hcells. unfold PvaS2_3b.cells12 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_3b.regs0 PvaS2_3b.regs_out12 60 KS_vaS2_3b_12 KS_vaS2_3b_12_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out12 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out12]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out12 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out12]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out12 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out12]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out12 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out12]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. right. right. right. right. right. right. left.
    change (SR.ps_pc PvaS2_3b.ps13) with 0x386b8 in Hms. change (SR.ps_regs PvaS2_3b.ps13) with (map (fun i => (i, nth i PvaS2_3b.regs_out13 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_3b.ps13) with PvaS2_3b.cells13 in Hcells. unfold PvaS2_3b.cells13 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_3b.regs0 PvaS2_3b.regs_out13 60 KS_vaS2_3b_13 KS_vaS2_3b_13_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out13 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out13]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out13 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out13]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out13 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out13]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. right. right. right. right. right. right. right. left.
    change (SR.ps_pc PvaS2_3b.ps14) with 0x386e0 in Hms. change (SR.ps_regs PvaS2_3b.ps14) with (map (fun i => (i, nth i PvaS2_3b.regs_out14 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_3b.ps14) with PvaS2_3b.cells14 in Hcells. unfold PvaS2_3b.cells14 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_3b.regs0 PvaS2_3b.regs_out14 60 KS_vaS2_3b_14 KS_vaS2_3b_14_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out14 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out14]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out14 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out14]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out14 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out14]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out14 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out14]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. right. right. right. right. right. right. right. right. left.
    change (SR.ps_pc PvaS2_3b.ps15) with 0x386b8 in Hms. change (SR.ps_regs PvaS2_3b.ps15) with (map (fun i => (i, nth i PvaS2_3b.regs_out15 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_3b.ps15) with PvaS2_3b.cells15 in Hcells. unfold PvaS2_3b.cells15 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_3b.regs0 PvaS2_3b.regs_out15 60 KS_vaS2_3b_15 KS_vaS2_3b_15_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out15 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out15]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out15 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out15]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out15 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out15]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out15 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out15]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. right. right. right. right. right. right. right. right. right. 
    change (SR.ps_pc PvaS2_3b.ps16) with 0x386e0 in Hms. change (SR.ps_regs PvaS2_3b.ps16) with (map (fun i => (i, nth i PvaS2_3b.regs_out16 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_3b.ps16) with PvaS2_3b.cells16 in Hcells. unfold PvaS2_3b.cells16 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_3b.regs0 PvaS2_3b.regs_out16 60 KS_vaS2_3b_16 KS_vaS2_3b_16_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out16 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out16]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out16 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out16]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out16 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out16]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_3b.regs_out16 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_3b.regs_out16]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvaS2_big := LibSegBs_vaS2_big_u.
Definition KS_vaS2_big_0 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_big.regs0 PvaS2_big.regs_out0).
Lemma KS_vaS2_big_0_ok : BG.kept_ok 60 PvaS2_big.regs0 PvaS2_big.regs_out0 KS_vaS2_big_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_big_1 : list nat := Eval vm_compute in (BG.kept_list 60 PvaS2_big.regs0 PvaS2_big.regs_out1).
Lemma KS_vaS2_big_1_ok : BG.kept_ok 60 PvaS2_big.regs0 PvaS2_big.regs_out1 KS_vaS2_big_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vaS2_big_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 2 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 13) = Z_to_bv 64 8 -> getr R (reg 14) = Z_to_bv 64 (-1) -> getr R (reg 15) = Z_to_bv 64 1 -> getr R (reg 16) = Z_to_bv 64 (-62) -> getr R (reg 17) = Z_to_bv 64 245 -> getr R (reg 18) = Z_to_bv 64 244 -> getr R (reg 19) = Z_to_bv 64 143 -> getr R (reg 20) = Z_to_bv 64 80240 -> getr R (reg 21) = Z_to_bv 64 (-80241) -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 24) = Z_to_bv 64 (V 37%nat) -> getr R (reg 25) = Z_to_bv 64 (V 38%nat) -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 4 <= (V 38%nat) <= 255 ->
  0 <= (V 37%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386e0 M')
        /\ (forall x, In x KS_vaS2_big_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 23) = Z_to_bv 64 (((V 33%nat) + (V 38%nat)) + 1)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + (V 38%nat))
        /\ getr R' (reg 27) = Z_to_bv 64 (((V 33%nat) + (V 38%nat)) + 1)
        /\ (V 38%nat) < (V 35%nat))
      \/ (msteps RSEGS (st fx R 0x38604 M) (st fx' R' 0x386e0 M')
        /\ (forall x, In x KS_vaS2_big_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 5
        /\ (V 35%nat) <= (V 38%nat))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G5 G6 G7 G8 G9 G10 G12 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G24 G25 G28 G29 G30 G31 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K1l; move K1l before pvzI7; pose proof (proj2 pvzI7) as K1r; move K1r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K2l; move K2l before pvzI8; pose proof (proj2 pvzI8) as K2r; move K2r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K4l; move K4l before pvzI10; pose proof (proj2 pvzI10) as K4r; move K4r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 37%nat => vz_37 | 38%nat => vz_38 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 39%nat. }
  assert (HR: regs_ok E PvaS2_big.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvaS2_big.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvaS2_big.kn0).
  { unfold know_ok, PvaS2_big.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvaS2_big.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvaS2_big.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvaS2_big.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PvaS2_big.ps0) with 0x386e0 in Hms. change (SR.ps_regs PvaS2_big.ps0) with (map (fun i => (i, nth i PvaS2_big.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_big.ps0) with PvaS2_big.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_big.regs0 PvaS2_big.regs_out0 60 KS_vaS2_big_0 KS_vaS2_big_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_big.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaS2_big.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_big.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaS2_big.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_big.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaS2_big.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaS2_big.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaS2_big.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  - right.
    change (SR.ps_pc PvaS2_big.ps1) with 0x386e0 in Hms. change (SR.ps_regs PvaS2_big.ps1) with (map (fun i => (i, nth i PvaS2_big.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaS2_big.ps1) with PvaS2_big.cells1 in Hcells. unfold PvaS2_big.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaS2_big.regs0 PvaS2_big.regs_out1 60 KS_vaS2_big_1 KS_vaS2_big_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaS2_big.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaS2_big.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvaB := LibSegBs_vaB_u.
Definition KS_vaB_0 : list nat := Eval vm_compute in (BG.kept_list 60 PvaB.regs0 PvaB.regs_out0).
Lemma KS_vaB_0_ok : BG.kept_ok 60 PvaB.regs0 PvaB.regs_out0 KS_vaB_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaB_1 : list nat := Eval vm_compute in (BG.kept_list 60 PvaB.regs0 PvaB.regs_out1).
Lemma KS_vaB_1_ok : BG.kept_ok 60 PvaB.regs0 PvaB.regs_out1 KS_vaB_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vaB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 2 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 10) = Z_to_bv 64 (V 37%nat) -> getr R (reg 12) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 13) = Z_to_bv 64 8 -> getr R (reg 14) = Z_to_bv 64 (-1) -> getr R (reg 15) = Z_to_bv 64 1 -> getr R (reg 16) = Z_to_bv 64 (-62) -> getr R (reg 17) = Z_to_bv 64 245 -> getr R (reg 18) = Z_to_bv 64 244 -> getr R (reg 19) = Z_to_bv 64 143 -> getr R (reg 20) = Z_to_bv 64 80240 -> getr R (reg 21) = Z_to_bv 64 (-80241) -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 23) = Z_to_bv 64 (V 33%nat) -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 0 <= (V 35%nat) <= 140737488355328 -> 0 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x386b8 M) (st fx' R' 0x386e0 M')
        /\ (forall x, In x KS_vaB_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + (V 35%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ (((V 33%nat) - (((V 33%nat) + (V 35%nat)) mod 2 ^ 64)) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0x386b8 M) (st fx' R' 0x3855c M')
        /\ (forall x, In x KS_vaB_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ 1 <= (((V 33%nat) - (((V 33%nat) + (V 35%nat)) mod 2 ^ 64)) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G12 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PvaB.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvaB.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvaB.kn0).
  { unfold know_ok, PvaB.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvaB.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvaB.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvaB.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PvaB.ps0) with 0x386e0 in Hms. change (SR.ps_regs PvaB.ps0) with (map (fun i => (i, nth i PvaB.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaB.ps0) with PvaB.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaB.regs0 PvaB.regs_out0 60 KS_vaB_0 KS_vaB_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaB.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvaB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvaB.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvaB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  - right.
    change (SR.ps_pc PvaB.ps1) with 0x3855c in Hms. change (SR.ps_regs PvaB.ps1) with (map (fun i => (i, nth i PvaB.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvaB.ps1) with PvaB.cells1 in Hcells. unfold PvaB.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaB.regs0 PvaB.regs_out1 60 KS_vaB_1 KS_vaB_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvaB.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PvaB.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvaX := LibSegBs_vaX_u.
Definition KS_vaX : list nat := Eval vm_compute in (BG.kept_list 60 PvaX.regs0 PvaX.regs_out0).
Lemma KS_vaX_ok : BG.kept_ok 60 PvaX.regs0 PvaX.regs_out0 KS_vaX = true. Proof. vm_compute. reflexivity. Qed.
Lemma vaX_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) ->
  140735332483168 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 53%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (V 54%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 55%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 56%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x386e0 M) (st fx' R' 0x38714 M')
        /\ (forall x, In x KS_vaX -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 53%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 54%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 55%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 56%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 G2 pvzI14 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV45l; move HV45l before pvzI2; pose proof (proj2 pvzI2) as HV45r; move HV45r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV46l; move HV46l before pvzI3; pose proof (proj2 pvzI3) as HV46r; move HV46r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV48l; move HV48l before pvzI5; pose proof (proj2 pvzI5) as HV48r; move HV48r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV49l; move HV49l before pvzI6; pose proof (proj2 pvzI6) as HV49r; move HV49r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV50l; move HV50l before pvzI7; pose proof (proj2 pvzI7) as HV50r; move HV50r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV51l; move HV51l before pvzI8; pose proof (proj2 pvzI8) as HV51r; move HV51r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV52l; move HV52l before pvzI9; pose proof (proj2 pvzI9) as HV52r; move HV52r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV53l; move HV53l before pvzI10; pose proof (proj2 pvzI10) as HV53r; move HV53r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV54l; move HV54l before pvzI11; pose proof (proj2 pvzI11) as HV54r; move HV54r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV55l; move HV55l before pvzI12; pose proof (proj2 pvzI12) as HV55r; move HV55r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV56l; move HV56l before pvzI13; pose proof (proj2 pvzI13) as HV56r; move HV56r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K0l; move K0l before pvzI14; pose proof (proj2 pvzI14) as K0r; move K0r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *. set (vz_54 := V 54%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | 54%nat => Z_to_bv 64 vz_54 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | 53%nat => vz_53 | 54%nat => vz_54 | 55%nat => vz_55 | 56%nat => vz_56 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 57%nat. }
  assert (HR: regs_ok E PvaX.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvaX.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvaX.kn0).
  { unfold know_ok, PvaX.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV54l HV54r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV55l HV55r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV56l HV56r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K14]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvaX.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvaX.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvaX.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvaX.ps0) with 0x38714 in Hms. change (SR.ps_regs PvaX.ps0) with (map (fun i => (i, nth i PvaX.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvaX.ps0) with PvaX.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvaX.regs0 PvaX.regs_out0 60 KS_vaX KS_vaX_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvaX.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PvaX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvaX.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PvaX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvaX.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PvaX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvaX.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PvaX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvaX.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PvaX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvaX.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PvaX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvaX.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PvaX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvaX.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PvaX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvaX.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PvaX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvaX.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PvaX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvaX.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PvaX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvaX.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PvaX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvaX.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PvaX.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

End PMVAP.
