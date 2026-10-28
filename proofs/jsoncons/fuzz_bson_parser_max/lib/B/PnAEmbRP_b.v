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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require LibSegBa_azrE0_b LibSegBa_azrE1_b LibSegBa_azrE2_b LibSegBa_azrE3_b LibSegBa_azrF1_b LibSegBa_azrF2_b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNAERP.
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
Module PazrE0 := LibSegBa_azrE0_b.
Definition KS_azrE0 : list nat := Eval vm_compute in (BG.kept_list 60 PazrE0.regs0 PazrE0.regs_out0).
Lemma KS_azrE0_ok : BG.kept_ok 60 PazrE0.regs0 PazrE0.regs_out0 KS_azrE0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma azrE0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) -> getr R (reg 13) = Z_to_bv 64 (V 52%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5.img_clear M 65536 1282048 ->
  L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 6905856 <= (V 33%nat) <= 140737488355295 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) -> (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) ->
  L5.u64_at RSEGS M (V 33%nat) 0 -> L5.u64_at RSEGS M ((V 33%nat) + 8) 0 -> L5.u64_at RSEGS M ((V 33%nat) + 16) 0 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 192) <= bv_unsigned a < ((V 2%nat) - 192) + 192) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 192) <= i < ((V 2%nat) - 192) + 192) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xad11c M) (st fx' R' 0x130338 M')
        /\ (forall x, In x KS_azrE0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 710136
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 176)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 9) = Z_to_bv 64 1
        /\ getr R' (reg 10) = Z_to_bv 64 40
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 1309752
        /\ getr R' (reg 13) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 14757395258967641293
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 19) = Z_to_bv 64 0
        /\ getr R' (reg 20) = Z_to_bv 64 ((((V 2%nat) - 80) / 8) + 2147450880)
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ getr R' (reg 23) = getr R (reg 23)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 709116
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G10 G11 G12 G13 pvzI6 K1 K2 K3 K4 K5 pvzI7 K7 K8 K9 K10 K11 K12 K13 K14 K15.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV52l; move HV52l before pvzI5; pose proof (proj2 pvzI5) as HV52r; move HV52r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K6l; move K6l before pvzI7; pose proof (proj2 pvzI7) as K6r; move K6r before pvzI7; clear pvzI7.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_52 := V 52%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 52%nat => Z_to_bv 64 vz_52 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 52%nat => vz_52 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 53%nat. }
  assert (HR: regs_ok E PazrE0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PazrE0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PazrE0.kn0).
  { unfold know_ok, PazrE0.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10 K11) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K10 K11; lia | clear - HV33l HV33r K6l K6r K8 K10 K11; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10 K11) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K10 K11; lia | clear - HV33l HV33r K6l K6r K8 K10 K11; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10 K11) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K10 K11; lia | clear - HV33l HV33r K6l K6r K8 K10 K11; lia | exactA K14]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | exactA K15]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PazrE0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PazrE0.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 192) <= bv_unsigned a < (vz_2 - 192) + 192) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PazrE0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K10 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PazrE0.ps0) with 0x130338 in Hms. change (SR.ps_regs PazrE0.ps0) with (map (fun i => (i, nth i PazrE0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PazrE0.ps0) with PazrE0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PazrE0.regs0 PazrE0.regs_out0 60 KS_azrE0 KS_azrE0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PazrE0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PazrE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE0.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PazrE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE0.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PazrE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE0.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PazrE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PazrE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PazrE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PazrE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE0.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PazrE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE0.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PazrE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE0.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PazrE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE0.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PazrE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE0.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PazrE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE0.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PazrE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE0.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PazrE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE0.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PazrE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE0.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PazrE0.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K10 K11) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K10 K11) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K10 K11) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk' ZA Hag ltac:(clear - HV52l HV52r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk' ZA Hag ltac:(clear - HV35l HV35r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K10 K11) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazrE1 := LibSegBa_azrE1_b.
Definition KS_azrE1 : list nat := Eval vm_compute in (BG.kept_list 60 PazrE1.regs0 PazrE1.regs_out0).
Lemma KS_azrE1_ok : BG.kept_ok 60 PazrE1.regs0 PazrE1.regs_out0 KS_azrE1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma azrE1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 176) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 9) = Z_to_bv 64 1 -> getr R (reg 10) = Z_to_bv 64 (V 40%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 19) = Z_to_bv 64 0 -> getr R (reg 20) = Z_to_bv 64 ((((V 2%nat) - 80) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 2147450880 -> getr R (reg 23) = Z_to_bv 64 (V 51%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 1249280 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 6905856 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) 0 -> L5.u64_at RSEGS M ((V 33%nat) + 8) 0 -> L5.u64_at RSEGS M ((V 33%nat) + 16) 0 ->
  6905856 <= (V 34%nat) <= 140737488355324 -> aligned (V 34%nat) 4 -> (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 4 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 ->
  L5.u32_at RSEGS M (V 34%nat) (V 38%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 34%nat) \/ (V 34%nat) + 4 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= (V 34%nat) \/ (V 34%nat) + 4 <= (V 33%nat)) -> 6905856 <= (V 35%nat) <= 140737488355324 ->
  aligned (V 35%nat) 4 -> (2147446784 + 17592186048512 <= (V 35%nat) \/ (V 35%nat) + 4 <= 2147446784) -> L5KA.zeros_at M (((V 35%nat) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M (V 35%nat) (V 39%nat) ->
  (((V 2%nat) - 4096) + 4096 <= (V 35%nat) \/ (V 35%nat) + 4 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= (V 35%nat) \/ (V 35%nat) + 4 <= (V 33%nat)) -> 6905856 <= (V 52%nat) <= 140737488355324 -> aligned (V 52%nat) 4 ->
  (2147446784 + 17592186048512 <= (V 52%nat) \/ (V 52%nat) + 4 <= 2147446784) -> L5KA.zeros_at M (((V 52%nat) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M (V 52%nat) (V 53%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 52%nat) \/ (V 52%nat) + 4 <= ((V 2%nat) - 4096)) ->
  ((V 33%nat) + 24 <= (V 52%nat) \/ (V 52%nat) + 4 <= (V 33%nat)) -> 0 <= (V 38%nat) <= 2147483647 -> 0 <= (V 39%nat) <= 2147483647 -> 0 <= (V 53%nat) <= 2147483647 ->
  4096 <= (V 40%nat) <= 140737488355288 -> aligned (V 40%nat) 16 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 40 <= 2147446784) -> L5KA.zeros_at M (((V 40%nat) / 8) + 2147450880) 5 ->
  L5.writable RSEGS M (V 40%nat) 40 -> (((V 2%nat) - 4096) + 4096 <= (V 40%nat) \/ (V 40%nat) + 40 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= (V 40%nat) \/ (V 40%nat) + 40 <= (V 33%nat)) -> (65536 + 6840320 <= (V 40%nat) \/ (V 40%nat) + 40 <= 65536) ->
  ((V 34%nat) + 4 <= (V 40%nat) \/ (V 40%nat) + 40 <= (V 34%nat)) -> ((V 35%nat) + 4 <= (V 40%nat) \/ (V 40%nat) + 40 <= (V 35%nat)) -> ((V 52%nat) + 4 <= (V 40%nat) \/ (V 40%nat) + 40 <= (V 52%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 120) 709116 -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 136) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 144) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 256) <= bv_unsigned a < ((V 2%nat) - 256) + 256) -> ~ (((V 40%nat) + 0) <= bv_unsigned a < ((V 40%nat) + 0) + 40) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 256) <= i < ((V 2%nat) - 256) + 256) -> ~ (((V 40%nat) + 0) <= i < ((V 40%nat) + 0) + 40) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xad5f8 M) (st fx' R' 0x77c94 M')
        /\ (forall x, In x KS_azrE1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 710644
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 192)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 40
        /\ getr R' (reg 15) = Z_to_bv 64 1
        /\ getr R' (reg 16) = Z_to_bv 64 (((V 33%nat) + 16) / 8)
        /\ getr R' (reg 17) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 2%nat) - 96)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 23) = Z_to_bv 64 ((((V 2%nat) - 96) / 8) + 2147450880)
        /\ getr R' (reg 24) = Z_to_bv 64 (((V 33%nat) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 709336
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 32) 0
        /\ L5.u8_at RSEGS M' ((V 40%nat) + 24) 0
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 16) (V 53%nat)
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 8) (V 39%nat)
        /\ L5.u32_at RSEGS M' (V 40%nat) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) ((V 40%nat) + 40)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 40%nat) + 40)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) (V 51%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) (bv_unsigned (getr R (reg 24)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 pvzI19 K1 K2 K3 K4 K5 K6 pvzI20 K8 K9 K10 K11 K12 K13 K14 K15 pvzI21 K17 K18 K19 K20 K21 K22 pvzI22 K24 K25 K26 K27 K28 K29 pvzI23 K31 K32 K33 K34 K35 K36 pvzI24 pvzI25 pvzI26 pvzI27 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57 K58 K59 K60 K61 K62 K63 K64 K65 K66 K67 K68.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV39l; move HV39l before pvzI6; pose proof (proj2 pvzI6) as HV39r; move HV39r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV40l; move HV40l before pvzI7; pose proof (proj2 pvzI7) as HV40r; move HV40r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV43l; move HV43l before pvzI8; pose proof (proj2 pvzI8) as HV43r; move HV43r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV44l; move HV44l before pvzI9; pose proof (proj2 pvzI9) as HV44r; move HV44r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV45l; move HV45l before pvzI10; pose proof (proj2 pvzI10) as HV45r; move HV45r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV46l; move HV46l before pvzI11; pose proof (proj2 pvzI11) as HV46r; move HV46r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV47l; move HV47l before pvzI12; pose proof (proj2 pvzI12) as HV47r; move HV47r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV48l; move HV48l before pvzI13; pose proof (proj2 pvzI13) as HV48r; move HV48r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV49l; move HV49l before pvzI14; pose proof (proj2 pvzI14) as HV49r; move HV49r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV50l; move HV50l before pvzI15; pose proof (proj2 pvzI15) as HV50r; move HV50r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV51l; move HV51l before pvzI16; pose proof (proj2 pvzI16) as HV51r; move HV51r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV52l; move HV52l before pvzI17; pose proof (proj2 pvzI17) as HV52r; move HV52r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV53l; move HV53l before pvzI18; pose proof (proj2 pvzI18) as HV53r; move HV53r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K0l; move K0l before pvzI19; pose proof (proj2 pvzI19) as K0r; move K0r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K7l; move K7l before pvzI20; pose proof (proj2 pvzI20) as K7r; move K7r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K16l; move K16l before pvzI21; pose proof (proj2 pvzI21) as K16r; move K16r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K23l; move K23l before pvzI22; pose proof (proj2 pvzI22) as K23r; move K23r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K30l; move K30l before pvzI23; pose proof (proj2 pvzI23) as K30r; move K30r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K37l; move K37l before pvzI24; pose proof (proj2 pvzI24) as K37r; move K37r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K38l; move K38l before pvzI25; pose proof (proj2 pvzI25) as K38r; move K38r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K39l; move K39l before pvzI26; pose proof (proj2 pvzI26) as K39r; move K39r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as K40l; move K40l before pvzI27; pose proof (proj2 pvzI27) as K40r; move K40r before pvzI27; clear pvzI27.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | 53%nat => vz_53 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 54%nat. }
  assert (HR: regs_ok E PazrE1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PazrE1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PazrE1.kn0).
  { unfold know_ok, PazrE1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45; lia | clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45; lia | clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45; lia | exactA K2]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45; lia | clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45; lia | clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K22 K29 K36 K46) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K22 K29 K36 K46) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K22 K29 K36 K46) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K22 K29 K36 K46) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 K22 K29 K36 K46; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K22 K29 K36 K46; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K22 K29 K36 K46; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K22 K29 K36 K46) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K22 K29 K36 K46) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K22 K29 K36 K46) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 K22 K29 K36 K46; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K22 K29 K36 K46; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K22 K29 K36 K46) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 K22 K29 K36 K46; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K22 K29 K36 K46; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K22 K29 K36 K46) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 K22 K29 K36 K46; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K22 K29 K36 K46; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18 K21 K22 K48) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18 K21 K22 K48) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18 K21 K22 K48) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18 K21 K22 K48) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K16l K16r K18 K21 K22 K48; lia | clear - HV34l HV34r K16l K16r K18 K21 K22 K48; lia | clear - HV34l HV34r K16l K16r K18 K21 K22 K48; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18 K21 K22 K48) | evalEk ZA ltac:(clear - HV38l HV38r K37l K37r) | clear - HV34l HV34r K16l K16r K18 K21 K22 K48; lia | clear - HV34l HV34r K16l K16r K18 K21 K22 K48; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18 K21 K22 K48) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K22 K29 K36 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18 K21 K22 K48) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K23l K23r K25 K28 K29 K49) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K23l K23r K25 K28 K29 K49) | clear; lia | exact K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K23l K23r K25 K28 K29 K49) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV35l HV35r K23l K23r K25 K28 K29 K49) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K23l K23r K25 K28 K29 K49; lia | clear - HV35l HV35r K23l K23r K25 K28 K29 K49; lia | clear - HV35l HV35r K23l K23r K25 K28 K29 K49; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV35l HV35r K23l K23r K25 K28 K29 K49) | evalEk ZA ltac:(clear - HV39l HV39r K38l K38r) | clear - HV35l HV35r K23l K23r K25 K28 K29 K49; lia | clear - HV35l HV35r K23l K23r K25 K28 K29 K49; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K23l K23r K25 K28 K29 K49) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K22 K29 K36 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K23l K23r K25 K28 K29 K49) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV52l HV52r K30l K30r K32 K35 K36 K50) | exact (conj K30l K30r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV52l HV52r K30l K30r K32 K35 K36 K50) | clear; lia | exact K31]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV52l HV52r K30l K30r K32 K35 K36 K50) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV52l HV52r K30l K30r K32 K35 K36 K50) | evalEk ZA ltac:(clear) | clear - HV52l HV52r K30l K30r K32 K35 K36 K50; lia | clear - HV52l HV52r K30l K30r K32 K35 K36 K50; lia | clear - HV52l HV52r K30l K30r K32 K35 K36 K50; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV52l HV52r K30l K30r K32 K35 K36 K50) | evalEk ZA ltac:(clear - HV53l HV53r K39l K39r) | clear - HV52l HV52r K30l K30r K32 K35 K36 K50; lia | clear - HV52l HV52r K30l K30r K32 K35 K36 K50; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV52l HV52r K30l K30r K32 K35 K36 K50) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K22 K29 K36 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV52l HV52r K30l K30r K32 K35 K36 K50) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K37l K37r) | exact (conj K37l K37r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K38l K38r) | exact (conj K38l K38r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV53l HV53r K39l K39r) | exact (conj K39l K39r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K40l K40r K42 K45 K46 K47 K48 K49 K50) | exact (conj K40l K40r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K40l K40r K42 K45 K46 K47 K48 K49 K50) | clear; lia | exact K41]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K40l K40r K42 K45 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K40l K40r K42 K45 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K40l K40r K42 K45 K46 K47 K48 K49 K50; lia | clear - HV40l HV40r K40l K40r K42 K45 K46 K47 K48 K49 K50; lia | clear - HV40l HV40r K40l K40r K42 K45 K46 K47 K48 K49 K50; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K40l K40r K42 K45 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K40l K40r K42 K45 K46 K47 K48 K49 K50; lia | clear - HV40l HV40r K40l K40r K42 K45 K46 K47 K48 K49 K50; lia | clear - HV40l HV40r K40l K40r K42 K45 K46 K47 K48 K49 K50; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K40l K40r K42 K45 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear) | generalize K45; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K22 K29 K36 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K40l K40r K42 K45 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K40l K40r K42 K45 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear) | generalize K47; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18 K21 K22 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K40l K40r K42 K45 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K23l K23r K25 K28 K29 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K40l K40r K42 K45 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV52l HV52r K30l K30r K32 K35 K36 K50) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K40l K40r K42 K45 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45; lia | clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45; lia | exactA K51]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45; lia | clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45; lia | clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45; lia | exactA K53]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45; lia | clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45; lia | clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45; lia | clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45; lia | clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45; lia | exactA K57]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45; lia | clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45; lia | exactA K58]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K22 K29 K36 K46) | clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45; lia | clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45; lia | exactA K59]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45; lia | clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45; lia | exactA K60]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45; lia | clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45; lia | exactA K61]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K22 K29 K36 K46) | clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45; lia | clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45; lia | exactA K62]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K22 K29 K36 K46) | clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45; lia | clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45; lia | exactA K63]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk ZA ltac:(clear - HV52l HV52r K30l K30r K32 K35 K36 K50) | clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45; lia | clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45; lia | exactA K64]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk ZA ltac:(clear - HV35l HV35r K23l K23r K25 K28 K29 K49) | clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45; lia | clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45; lia | exactA K65]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18 K21 K22 K48) | clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45; lia | clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45; lia | exactA K66]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K22 K29 K36 K46) | clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45; lia | clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45; lia | exactA K67]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K68]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PazrE1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PazrE1.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 256) <= bv_unsigned a < (vz_2 - 256) + 256) -> ~ ((vz_40 + 0) <= bv_unsigned a < (vz_40 + 0) + 40) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PazrE1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K40l K40r K42 K45 K46 K47 K48 K49 K50) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K40l K40r K42 K45 K46 K47 K48 K49 K50 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PazrE1.ps0) with 0x77c94 in Hms. change (SR.ps_regs PazrE1.ps0) with (map (fun i => (i, nth i PazrE1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PazrE1.ps0) with PazrE1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PazrE1.regs0 PazrE1.regs_out0 60 KS_azrE1 KS_azrE1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PazrE1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PazrE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE1.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PazrE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE1.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PazrE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE1.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PazrE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PazrE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PazrE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE1.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PazrE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE1.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PazrE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE1.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PazrE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE1.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PazrE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE1.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PazrE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE1.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PazrE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE1.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PazrE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE1.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PazrE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE1.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PazrE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE1.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PazrE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE1.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PazrE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk' ZA Hag ltac:(clear - HV35l HV35r K23l K23r K25 K28 K29 K49) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk' ZA Hag ltac:(clear - HV52l HV52r K30l K30r K32 K35 K36 K50) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K22 K29 K36 K46) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K22 K29 K36 K46) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K40l K40r K42 K45 K46 K47 K48 K49 K50) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K40l K40r K42 K45 K46 K47 K48 K49 K50) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K40l K40r K42 K45 K46 K47 K48 K49 K50) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K40l K40r K42 K45 K46 K47 K48 K49 K50) | evalEk' ZA Hag ltac:(clear - HV53l HV53r K39l K39r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K40l K40r K42 K45 K46 K47 K48 K49 K50) | evalEk' ZA Hag ltac:(clear - HV39l HV39r K38l K38r) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K40l K40r K42 K45 K46 K47 K48 K49 K50) | evalEk' ZA Hag ltac:(clear - HV38l HV38r K37l K37r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K40l K40r K42 K45 K46 K47 K48 K49 K50) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K40l K40r K42 K45 K46 K47 K48 K49 K50) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 23%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk' ZA Hag ltac:(clear - HV47l HV47r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 24%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 25%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk' ZA Hag ltac:(clear - HV49l HV49r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 26%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk' ZA Hag ltac:(clear - HV50l HV50r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 27%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K22 K29 K36 K46) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K40l K40r K42 K45 K46 K47 K48 K49 K50) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K16l K16r K18 K21 K22 K48) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K22 K29 K36 K46) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk' ZA Hag ltac:(clear - HV51l HV51r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K21 K28 K35 K45) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazrE2 := LibSegBa_azrE2_b.
Definition KS_azrE2 : list nat := Eval vm_compute in (BG.kept_list 60 PazrE2.regs0 PazrE2.regs_out0).
Lemma KS_azrE2_ok : BG.kept_ok 60 PazrE2.regs0 PazrE2.regs_out0 KS_azrE2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma azrE2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 24%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 9) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 19) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 20) = Z_to_bv 64 (V 40%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 ((((V 2%nat) - 96) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (((V 33%nat) / 8) + 2147450880) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 6905856 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.writable RSEGS M (V 33%nat) 24 -> L5.u64_at RSEGS M (V 33%nat) 0 -> L5.u64_at RSEGS M ((V 33%nat) + 8) 0 ->
  L5.u64_at RSEGS M ((V 33%nat) + 16) 0 -> 4096 <= (V 40%nat) <= 140737488355288 -> aligned (V 40%nat) 16 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 40 <= 2147446784) ->
  L5KA.zeros_at M (((V 40%nat) / 8) + 2147450880) 5 -> L5.writable RSEGS M (V 40%nat) 40 -> (((V 2%nat) - 4096) + 4096 <= (V 40%nat) \/ (V 40%nat) + 40 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= (V 40%nat) \/ (V 40%nat) + 40 <= (V 33%nat)) ->
  (65536 + 6840320 <= (V 40%nat) \/ (V 40%nat) + 40 <= 65536) -> ((V 34%nat) + 4 <= (V 40%nat) \/ (V 40%nat) + 40 <= (V 34%nat)) -> ((V 35%nat) + 4 <= (V 40%nat) \/ (V 40%nat) + 40 <= (V 35%nat)) -> ((V 52%nat) + 4 <= (V 40%nat) \/ (V 40%nat) + 40 <= (V 52%nat)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) ((V 40%nat) + 40) -> L5.u64_at RSEGS M ((V 2%nat) - 88) ((V 40%nat) + 40) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 40%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 104) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 709336 -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 136) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 144) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880) ->
  L5.u64_at RSEGS M ((V 2%nat) - 176) 2147450880 -> L5.u64_at RSEGS M ((V 2%nat) - 184) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 24%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 256) <= bv_unsigned a < ((V 2%nat) - 256) + 256) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 256) <= i < ((V 2%nat) - 256) + 256) -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xad7f4 M) (st fx' R' 0x7ba7c M')
        /\ (forall x, In x KS_azrE2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 711480
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 5) = Z_to_bv 64 0
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + 40)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 40%nat) + 40)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 40%nat) + 40)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 16) = Z_to_bv 64 1
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 40%nat) + 40)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ getr R' (reg 23) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 24%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 709336
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 16) ((V 40%nat) + 40)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) ((V 40%nat) + 40)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) 0
        /\ L5.u64_at RSEGS M' (V 33%nat) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 pvzI17 K1 K2 K3 K4 K5 K6 pvzI18 K8 K9 K10 K11 K12 K13 K14 K15 K16 pvzI19 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV24l; move HV24l before pvzI2; pose proof (proj2 pvzI2) as HV24r; move HV24r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV35l; move HV35l before pvzI5; pose proof (proj2 pvzI5) as HV35r; move HV35r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV40l; move HV40l before pvzI6; pose proof (proj2 pvzI6) as HV40r; move HV40r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV43l; move HV43l before pvzI7; pose proof (proj2 pvzI7) as HV43r; move HV43r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV44l; move HV44l before pvzI8; pose proof (proj2 pvzI8) as HV44r; move HV44r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV45l; move HV45l before pvzI9; pose proof (proj2 pvzI9) as HV45r; move HV45r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV46l; move HV46l before pvzI10; pose proof (proj2 pvzI10) as HV46r; move HV46r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV47l; move HV47l before pvzI11; pose proof (proj2 pvzI11) as HV47r; move HV47r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV48l; move HV48l before pvzI12; pose proof (proj2 pvzI12) as HV48r; move HV48r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV49l; move HV49l before pvzI13; pose proof (proj2 pvzI13) as HV49r; move HV49r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV50l; move HV50l before pvzI14; pose proof (proj2 pvzI14) as HV50r; move HV50r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV51l; move HV51l before pvzI15; pose proof (proj2 pvzI15) as HV51r; move HV51r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV52l; move HV52l before pvzI16; pose proof (proj2 pvzI16) as HV52r; move HV52r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K0l; move K0l before pvzI17; pose proof (proj2 pvzI17) as K0r; move K0r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K7l; move K7l before pvzI18; pose proof (proj2 pvzI18) as K7r; move K7r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K17l; move K17l before pvzI19; pose proof (proj2 pvzI19) as K17r; move K17r before pvzI19; clear pvzI19.
  set (vz_2 := V 2%nat) in *. set (vz_24 := V 24%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 24%nat => Z_to_bv 64 vz_24 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 40%nat => Z_to_bv 64 vz_40 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 24%nat => vz_24 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 40%nat => vz_40 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 53%nat. }
  assert (HR: regs_ok E PazrE2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PazrE2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PazrE2.kn0).
  { unfold know_ok, PazrE2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K22) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K22) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K22) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K22; lia | clear - HV2l HV2r K0l K0r K11 K22; lia | clear - HV2l HV2r K0l K0r K11 K22; lia | exactA K2]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K22) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K22; lia | clear - HV2l HV2r K0l K0r K11 K22; lia | clear - HV2l HV2r K0l K0r K11 K22; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K23) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K23) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K23) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K23) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 K23; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K23; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K23; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K22) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K23) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K23) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K23) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 K23; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K23; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K23; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K23) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 K23; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K23; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K23) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 K23; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K23; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K23) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 K23; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K23; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K17l K17r K19 K22 K23 K24 K25 K26 K27) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K17l K17r K19 K22 K23 K24 K25 K26 K27) | clear; lia | exact K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K17l K17r K19 K22 K23 K24 K25 K26 K27) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K17l K17r K19 K22 K23 K24 K25 K26 K27) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K17l K17r K19 K22 K23 K24 K25 K26 K27; lia | clear - HV40l HV40r K17l K17r K19 K22 K23 K24 K25 K26 K27; lia | clear - HV40l HV40r K17l K17r K19 K22 K23 K24 K25 K26 K27; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K17l K17r K19 K22 K23 K24 K25 K26 K27) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K17l K17r K19 K22 K23 K24 K25 K26 K27; lia | clear - HV40l HV40r K17l K17r K19 K22 K23 K24 K25 K26 K27; lia | clear - HV40l HV40r K17l K17r K19 K22 K23 K24 K25 K26 K27; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K22) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K17l K17r K19 K22 K23 K24 K25 K26 K27) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K17l K17r K19 K22 K23 K24 K25 K26 K27) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K17l K17r K19 K22 K23 K24 K25 K26 K27) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K25) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K17l K17r K19 K22 K23 K24 K25 K26 K27) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K17l K17r K19 K22 K23 K24 K25 K26 K27) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV52l HV52r K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K17l K17r K19 K22 K23 K24 K25 K26 K27) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K22) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K11 K22; lia | clear - HV2l HV2r K0l K0r K11 K22; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K22) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K11 K22; lia | clear - HV2l HV2r K0l K0r K11 K22; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K22) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K11 K22; lia | clear - HV2l HV2r K0l K0r K11 K22; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K22) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K11 K22; lia | clear - HV2l HV2r K0l K0r K11 K22; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K22) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K11 K22; lia | clear - HV2l HV2r K0l K0r K11 K22; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K22) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K11 K22; lia | clear - HV2l HV2r K0l K0r K11 K22; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K22) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K11 K22; lia | clear - HV2l HV2r K0l K0r K11 K22; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K22) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K11 K22; lia | clear - HV2l HV2r K0l K0r K11 K22; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K22) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K23) | clear - HV2l HV2r K0l K0r K11 K22; lia | clear - HV2l HV2r K0l K0r K11 K22; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K22) | evalEk ZA ltac:(clear - HV40l HV40r K17l K17r K19 K22 K23 K24 K25 K26 K27) | clear - HV2l HV2r K0l K0r K11 K22; lia | clear - HV2l HV2r K0l K0r K11 K22; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K22) | evalEk ZA ltac:(clear - HV40l HV40r K17l K17r K19 K22 K23 K24 K25 K26 K27) | clear - HV2l HV2r K0l K0r K11 K22; lia | clear - HV2l HV2r K0l K0r K11 K22; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K22) | evalEk ZA ltac:(clear - HV40l HV40r K17l K17r K19 K22 K23 K24 K25 K26 K27) | clear - HV2l HV2r K0l K0r K11 K22; lia | clear - HV2l HV2r K0l K0r K11 K22; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K22) | evalEk ZA ltac:(clear - HV40l HV40r K17l K17r K19 K22 K23 K24 K25 K26 K27) | clear - HV2l HV2r K0l K0r K11 K22; lia | clear - HV2l HV2r K0l K0r K11 K22; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K22) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K22; lia | clear - HV2l HV2r K0l K0r K11 K22; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K22) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K23) | clear - HV2l HV2r K0l K0r K11 K22; lia | clear - HV2l HV2r K0l K0r K11 K22; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K22) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K23) | clear - HV2l HV2r K0l K0r K11 K22; lia | clear - HV2l HV2r K0l K0r K11 K22; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K22) | evalEk ZA ltac:(clear - HV52l HV52r K27) | clear - HV2l HV2r K0l K0r K11 K22; lia | clear - HV2l HV2r K0l K0r K11 K22; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K22) | evalEk ZA ltac:(clear - HV35l HV35r K26) | clear - HV2l HV2r K0l K0r K11 K22; lia | clear - HV2l HV2r K0l K0r K11 K22; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K22) | evalEk ZA ltac:(clear - HV34l HV34r K25) | clear - HV2l HV2r K0l K0r K11 K22; lia | clear - HV2l HV2r K0l K0r K11 K22; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K22) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K23) | clear - HV2l HV2r K0l K0r K11 K22; lia | clear - HV2l HV2r K0l K0r K11 K22; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K22) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K22; lia | clear - HV2l HV2r K0l K0r K11 K22; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K22) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r K11 K22; lia | clear - HV2l HV2r K0l K0r K11 K22; lia | exactA K49]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K22) | evalEk ZA ltac:(clear - HV24l HV24r) | clear - HV2l HV2r K0l K0r K11 K22; lia | clear - HV2l HV2r K0l K0r K11 K22; lia | exactA K50]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PazrE2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PazrE2.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 256) <= bv_unsigned a < (vz_2 - 256) + 256) -> ~ ((vz_33 + 0) <= bv_unsigned a < (vz_33 + 0) + 24) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PazrE2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K22) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K22 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K23) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 K23 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PazrE2.ps0) with 0x7ba7c in Hms. change (SR.ps_regs PazrE2.ps0) with (map (fun i => (i, nth i PazrE2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PazrE2.ps0) with PazrE2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PazrE2.regs0 PazrE2.regs_out0 60 KS_azrE2 KS_azrE2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PazrE2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PazrE2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE2.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PazrE2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE2.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PazrE2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE2.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PazrE2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PazrE2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PazrE2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PazrE2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE2.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PazrE2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE2.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PazrE2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE2.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PazrE2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE2.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PazrE2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE2.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PazrE2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE2.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PazrE2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE2.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PazrE2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE2.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PazrE2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE2.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PazrE2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE2.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PazrE2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE2.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PazrE2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE2.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PazrE2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K22) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K23) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K23) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K17l K17r K19 K22 K23 K24 K25 K26 K27) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K23) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K17l K17r K19 K22 K23 K24 K25 K26 K27) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K23) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K17l K17r K19 K22 K23 K24 K25 K26 K27) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K22) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K22) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K22) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K22) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K22) | evalEk' ZA Hag ltac:(clear - HV47l HV47r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K22) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K22) | evalEk' ZA Hag ltac:(clear - HV49l HV49r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K22) | evalEk' ZA Hag ltac:(clear - HV50l HV50r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K22) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K23) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazrE3 := LibSegBa_azrE3_b.
Definition KS_azrE3 : list nat := Eval vm_compute in (BG.kept_list 60 PazrE3.regs0 PazrE3.regs_out0).
Lemma KS_azrE3_ok : BG.kept_ok 60 PazrE3.regs0 PazrE3.regs_out0 KS_azrE3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma azrE3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 9) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 (V 52%nat) -> getr R (reg 19) = Z_to_bv 64 (V 35%nat) -> getr R (reg 20) = Z_to_bv 64 (V 34%nat) -> getr R (reg 21) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 2147450880 -> getr R (reg 23) = Z_to_bv 64 (V 51%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 1249280 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 6905856 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.writable RSEGS M (V 33%nat) 24 -> L5.u64_at RSEGS M (V 33%nat) (V 40%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 40%nat) + 40) ->
  L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 40%nat) + 40) -> 4096 <= (V 40%nat) <= 140737488355248 -> aligned (V 40%nat) 16 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 88) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 96) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 104) 0 ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) 709336 -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) -> L5.img_clear M 65536 1282048 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 256) <= bv_unsigned a < ((V 2%nat) - 256) + 256) -> ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 256) <= i < ((V 2%nat) - 256) + 256) -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xadb38 M) (st fx' R' 0xad314 M')
        /\ (forall x, In x KS_azrE3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 40%nat) + 40)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 72)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 2147450880
        /\ getr R' (reg 14) = Z_to_bv 64 (((V 2%nat) - 72) / 8)
        /\ getr R' (reg 15) = Z_to_bv 64 ((((V 2%nat) - 88) / 8) + 2147450880)
        /\ getr R' (reg 16) = Z_to_bv 64 0
        /\ getr R' (reg 17) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 51%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) ((V 40%nat) + 40)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 G2 G8 G9 G18 G19 G20 G21 G22 G23 pvzI16 K1 K2 K3 K4 K5 K6 pvzI17 K8 K9 K10 K11 K12 K13 K14 K15 K16 pvzI18 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV40l; move HV40l before pvzI5; pose proof (proj2 pvzI5) as HV40r; move HV40r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV43l; move HV43l before pvzI6; pose proof (proj2 pvzI6) as HV43r; move HV43r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV44l; move HV44l before pvzI7; pose proof (proj2 pvzI7) as HV44r; move HV44r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV45l; move HV45l before pvzI8; pose proof (proj2 pvzI8) as HV45r; move HV45r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV46l; move HV46l before pvzI9; pose proof (proj2 pvzI9) as HV46r; move HV46r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV47l; move HV47l before pvzI10; pose proof (proj2 pvzI10) as HV47r; move HV47r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV48l; move HV48l before pvzI11; pose proof (proj2 pvzI11) as HV48r; move HV48r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV49l; move HV49l before pvzI12; pose proof (proj2 pvzI12) as HV49r; move HV49r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV50l; move HV50l before pvzI13; pose proof (proj2 pvzI13) as HV50r; move HV50r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV51l; move HV51l before pvzI14; pose proof (proj2 pvzI14) as HV51r; move HV51r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV52l; move HV52l before pvzI15; pose proof (proj2 pvzI15) as HV52r; move HV52r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K0l; move K0l before pvzI16; pose proof (proj2 pvzI16) as K0r; move K0r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K7l; move K7l before pvzI17; pose proof (proj2 pvzI17) as K7r; move K7r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K17l; move K17l before pvzI18; pose proof (proj2 pvzI18) as K17r; move K17r before pvzI18; clear pvzI18.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 40%nat => Z_to_bv 64 vz_40 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 40%nat => vz_40 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 53%nat. }
  assert (HR: regs_ok E PazrE3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PazrE3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PazrE3.kn0).
  { unfold know_ok, PazrE3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K2]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV40l HV40r K17l K17r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV40l HV40r K17l K17r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV40l HV40r K17l K17r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K17l K17r) | clear; lia | exact K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K34]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PazrE3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PazrE3.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 256) <= bv_unsigned a < (vz_2 - 256) + 256) -> ~ ((vz_33 + 8) <= bv_unsigned a < (vz_33 + 8) + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PazrE3.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PazrE3.ps0) with 0xad314 in Hms. change (SR.ps_regs PazrE3.ps0) with (map (fun i => (i, nth i PazrE3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PazrE3.ps0) with PazrE3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PazrE3.regs0 PazrE3.regs_out0 60 KS_azrE3 KS_azrE3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PazrE3.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PazrE3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE3.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PazrE3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE3.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PazrE3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE3.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PazrE3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PazrE3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PazrE3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE3.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PazrE3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE3.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PazrE3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE3.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PazrE3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE3.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PazrE3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE3.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PazrE3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE3.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PazrE3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE3.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PazrE3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE3.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PazrE3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE3.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PazrE3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE3.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PazrE3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE3.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PazrE3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrE3.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PazrE3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K17l K17r) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazrF1 := LibSegBa_azrF1_b.
Definition KS_azrF1 : list nat := Eval vm_compute in (BG.kept_list 60 PazrF1.regs0 PazrF1.regs_out0).
Lemma KS_azrF1_ok : BG.kept_ok 60 PazrF1.regs0 PazrF1.regs_out0 KS_azrF1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma azrF1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) -> getr R (reg 13) = Z_to_bv 64 (V 52%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 1249280 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 6905856 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + (V 37%nat)) -> L5.u64_at RSEGS M ((V 33%nat) + 16) (V 41%nat) ->
  4096 <= (V 36%nat) <= 140737488355288 -> aligned (V 36%nat) 16 -> 0 <= (V 37%nat) <= 81880 -> aligned (V 37%nat) 8 ->
  4136 <= (V 41%nat) <= 140737488355327 -> 40 <= ((V 41%nat) - ((V 36%nat) + (V 37%nat))) <= 81920 -> 0 <= ((V 41%nat) - (V 36%nat)) <= 163840 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xacf40 M) (st fx' R' 0x7ba7c M')
        /\ (forall x, In x KS_azrF1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 709968
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 36%nat) + (V 37%nat))
        /\ getr R' (reg 13) = Z_to_bv 64 (((V 36%nat) + (V 37%nat)) + 40)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 16) = Z_to_bv 64 (((V 36%nat) + (V 37%nat)) + 40)
        /\ getr R' (reg 17) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 2147450880
        /\ getr R' (reg 20) = getr R (reg 20)
        /\ getr R' (reg 21) = getr R (reg 21)
        /\ getr R' (reg 22) = getr R (reg 22)
        /\ getr R' (reg 23) = getr R (reg 23)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 708524
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) ((V 36%nat) + (V 37%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (((V 36%nat) + (V 37%nat)) + 40)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 52%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G10 G11 G12 G13 pvzI9 K1 K2 K3 K4 K5 K6 pvzI10 K8 K9 K10 K11 K12 K13 K14 K15 pvzI11 K17 pvzI12 K19 pvzI13 pvzI14 pvzI15.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV37l; move HV37l before pvzI6; pose proof (proj2 pvzI6) as HV37r; move HV37r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV41l; move HV41l before pvzI7; pose proof (proj2 pvzI7) as HV41r; move HV41r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV52l; move HV52l before pvzI8; pose proof (proj2 pvzI8) as HV52r; move HV52r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K0l; move K0l before pvzI9; pose proof (proj2 pvzI9) as K0r; move K0r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K7l; move K7l before pvzI10; pose proof (proj2 pvzI10) as K7r; move K7r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K16l; move K16l before pvzI11; pose proof (proj2 pvzI11) as K16r; move K16r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K18l; move K18l before pvzI12; pose proof (proj2 pvzI12) as K18r; move K18r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K20l; move K20l before pvzI13; pose proof (proj2 pvzI13) as K20r; move K20r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K21l; move K21l before pvzI14; pose proof (proj2 pvzI14) as K21r; move K21r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K22l; move K22l before pvzI15; pose proof (proj2 pvzI15) as K22r; move K22r before pvzI15; clear pvzI15.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_52 := V 52%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 41%nat => Z_to_bv 64 vz_41 | 52%nat => Z_to_bv 64 vz_52 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 41%nat => vz_41 | 52%nat => vz_52 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 53%nat. }
  assert (HR: regs_ok E PazrF1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PazrF1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PazrF1.kn0).
  { unfold know_ok, PazrF1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K2]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r K21l K21r K22l K22r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r K21l K21r K22l K22r HV37l HV37r K18l K18r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV41l HV41r K20l K20r K21l K21r K22l K22r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r K21l K21r K22l K22r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r K21l K21r K22l K22r) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K18l K18r K21l K21r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K18l K18r K21l K21r) | clear; lia | exact K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K20l K20r K21l K21r K22l K22r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r K21l K21r K22l K22r HV37l HV37r K18l K18r HV41l HV41r K20l K20r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r K21l K21r K22l K22r HV41l HV41r K20l K20r) | exact (conj K22l K22r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PazrF1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PazrF1.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 128) <= bv_unsigned a < (vz_2 - 128) + 128) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PazrF1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PazrF1.ps0) with 0x7ba7c in Hms. change (SR.ps_regs PazrF1.ps0) with (map (fun i => (i, nth i PazrF1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PazrF1.ps0) with PazrF1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PazrF1.regs0 PazrF1.regs_out0 60 KS_azrF1 KS_azrF1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PazrF1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PazrF1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrF1.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PazrF1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrF1.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PazrF1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrF1.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PazrF1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrF1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PazrF1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrF1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PazrF1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrF1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PazrF1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrF1.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PazrF1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrF1.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PazrF1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrF1.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PazrF1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrF1.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PazrF1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrF1.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PazrF1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrF1.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PazrF1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrF1.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PazrF1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrF1.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PazrF1.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PazrF1.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PazrF1.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PazrF1.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PazrF1.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PazrF1.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PazrF1.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K16l K16r K21l K21r K22l K22r HV37l HV37r K18l K18r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K16l K16r K21l K21r K22l K22r HV37l HV37r K18l K18r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV52l HV52r) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazrF2 := LibSegBa_azrF2_b.
Definition KS_azrF2 : list nat := Eval vm_compute in (BG.kept_list 60 PazrF2.regs0 PazrF2.regs_out0).
Lemma KS_azrF2_ok : BG.kept_ok 60 PazrF2.regs0 PazrF2.regs_out0 KS_azrF2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma azrF2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 52%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 (V 48%nat) -> getr R (reg 21) = Z_to_bv 64 (V 49%nat) -> getr R (reg 22) = Z_to_bv 64 (V 50%nat) -> getr R (reg 23) = Z_to_bv 64 (V 51%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 1249280 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 6905856 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.writable RSEGS M (V 33%nat) 24 -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + (V 37%nat)) ->
  L5.u64_at RSEGS M ((V 33%nat) + 16) (V 41%nat) -> 4096 <= (V 36%nat) <= 140737488355288 -> aligned (V 36%nat) 16 -> 6905856 <= (V 34%nat) <= 140737488355324 ->
  aligned (V 34%nat) 4 -> (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 4 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M (V 34%nat) (V 38%nat) ->
  (((V 2%nat) - 4096) + 4096 <= (V 34%nat) \/ (V 34%nat) + 4 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= (V 34%nat) \/ (V 34%nat) + 4 <= (V 33%nat)) -> 6905856 <= (V 35%nat) <= 140737488355324 -> aligned (V 35%nat) 4 ->
  (2147446784 + 17592186048512 <= (V 35%nat) \/ (V 35%nat) + 4 <= 2147446784) -> L5KA.zeros_at M (((V 35%nat) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M (V 35%nat) (V 39%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 35%nat) \/ (V 35%nat) + 4 <= ((V 2%nat) - 4096)) ->
  ((V 33%nat) + 24 <= (V 35%nat) \/ (V 35%nat) + 4 <= (V 33%nat)) -> 6905856 <= (V 52%nat) <= 140737488355324 -> aligned (V 52%nat) 4 -> (2147446784 + 17592186048512 <= (V 52%nat) \/ (V 52%nat) + 4 <= 2147446784) ->
  L5KA.zeros_at M (((V 52%nat) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M (V 52%nat) (V 53%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 52%nat) \/ (V 52%nat) + 4 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= (V 52%nat) \/ (V 52%nat) + 4 <= (V 33%nat)) ->
  0 <= (V 38%nat) <= 2147483647 -> 0 <= (V 39%nat) <= 2147483647 -> 0 <= (V 53%nat) <= 2147483647 -> 0 <= (V 37%nat) <= 81880 ->
  aligned (V 37%nat) 8 -> 4136 <= (V 41%nat) <= 140737488355327 -> 40 <= ((V 41%nat) - ((V 36%nat) + (V 37%nat))) <= 81920 -> L5KA.zeros_at M ((((V 36%nat) + (V 37%nat)) / 8) + 2147450880) 5 ->
  L5.writable RSEGS M ((V 36%nat) + (V 37%nat)) 40 -> (2147446784 + 17592186048512 <= ((V 36%nat) + (V 37%nat)) \/ ((V 36%nat) + (V 37%nat)) + 40 <= 2147446784) -> (65536 + 6840320 <= ((V 36%nat) + (V 37%nat)) \/ ((V 36%nat) + (V 37%nat)) + 40 <= 65536) -> 4096 <= ((V 36%nat) + (V 37%nat)) <= 140737488355288 ->
  (((V 2%nat) - 4096) + 4096 <= ((V 36%nat) + (V 37%nat)) \/ ((V 36%nat) + (V 37%nat)) + 40 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= ((V 36%nat) + (V 37%nat)) \/ ((V 36%nat) + (V 37%nat)) + 40 <= (V 33%nat)) -> ((V 34%nat) + 4 <= ((V 36%nat) + (V 37%nat)) \/ ((V 36%nat) + (V 37%nat)) + 40 <= (V 34%nat)) -> ((V 35%nat) + 4 <= ((V 36%nat) + (V 37%nat)) \/ ((V 36%nat) + (V 37%nat)) + 40 <= (V 35%nat)) ->
  ((V 52%nat) + 4 <= ((V 36%nat) + (V 37%nat)) \/ ((V 36%nat) + (V 37%nat)) + 40 <= (V 52%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (((V 36%nat) + (V 37%nat)) + 40) -> L5.u64_at RSEGS M ((V 2%nat) - 56) ((V 36%nat) + (V 37%nat)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) 708524 -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 52%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((((V 36%nat) + (V 37%nat)) + 0) <= bv_unsigned a < (((V 36%nat) + (V 37%nat)) + 0) + 40) -> ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 8) -> ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((((V 36%nat) + (V 37%nat)) + 0) <= i < (((V 36%nat) + (V 37%nat)) + 0) + 40) -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 8) -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xad550 M) (st fx' R' 0xad09c M')
        /\ (forall x, In x KS_azrF2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 36%nat) + (V 37%nat)) + 40)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 (((V 36%nat) + (V 37%nat)) + 40)
        /\ getr R' (reg 14) = Z_to_bv 64 2147450880
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 51%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) (((V 36%nat) + (V 37%nat)) + 40)
        /\ L5.u64_at RSEGS M' (((V 36%nat) + (V 37%nat)) + 32) 0
        /\ L5.u8_at RSEGS M' (((V 36%nat) + (V 37%nat)) + 24) 0
        /\ L5.u64_at RSEGS M' (((V 36%nat) + (V 37%nat)) + 16) (V 53%nat)
        /\ L5.u64_at RSEGS M' (((V 36%nat) + (V 37%nat)) + 8) (V 39%nat)
        /\ L5.u32_at RSEGS M' ((V 36%nat) + (V 37%nat)) (V 38%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 pvzI20 G2 G8 G9 G18 G19 G20 G21 G22 G23 pvzI21 K1 K2 K3 K4 K5 K6 pvzI22 K8 K9 K10 K11 K12 K13 K14 K15 K16 pvzI23 K18 pvzI24 K20 K21 K22 K23 K24 K25 pvzI25 K27 K28 K29 K30 K31 K32 pvzI26 K34 K35 K36 K37 K38 K39 pvzI27 pvzI28 pvzI29 pvzI30 K44 pvzI31 pvzI32 K47 K48 K49 K50 pvzI33 K52 K53 K54 K55 K56 K57 K58 K59 K60 K61 K62 K63 K64 K65 K66.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV37l; move HV37l before pvzI6; pose proof (proj2 pvzI6) as HV37r; move HV37r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV38l; move HV38l before pvzI7; pose proof (proj2 pvzI7) as HV38r; move HV38r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV39l; move HV39l before pvzI8; pose proof (proj2 pvzI8) as HV39r; move HV39r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV41l; move HV41l before pvzI9; pose proof (proj2 pvzI9) as HV41r; move HV41r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV43l; move HV43l before pvzI10; pose proof (proj2 pvzI10) as HV43r; move HV43r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV44l; move HV44l before pvzI11; pose proof (proj2 pvzI11) as HV44r; move HV44r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV45l; move HV45l before pvzI12; pose proof (proj2 pvzI12) as HV45r; move HV45r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV46l; move HV46l before pvzI13; pose proof (proj2 pvzI13) as HV46r; move HV46r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV47l; move HV47l before pvzI14; pose proof (proj2 pvzI14) as HV47r; move HV47r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV48l; move HV48l before pvzI15; pose proof (proj2 pvzI15) as HV48r; move HV48r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV49l; move HV49l before pvzI16; pose proof (proj2 pvzI16) as HV49r; move HV49r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV50l; move HV50l before pvzI17; pose proof (proj2 pvzI17) as HV50r; move HV50r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV51l; move HV51l before pvzI18; pose proof (proj2 pvzI18) as HV51r; move HV51r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV52l; move HV52l before pvzI19; pose proof (proj2 pvzI19) as HV52r; move HV52r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as HV53l; move HV53l before pvzI20; pose proof (proj2 pvzI20) as HV53r; move HV53r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K0l; move K0l before pvzI21; pose proof (proj2 pvzI21) as K0r; move K0r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K7l; move K7l before pvzI22; pose proof (proj2 pvzI22) as K7r; move K7r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K17l; move K17l before pvzI23; pose proof (proj2 pvzI23) as K17r; move K17r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K19l; move K19l before pvzI24; pose proof (proj2 pvzI24) as K19r; move K19r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K26l; move K26l before pvzI25; pose proof (proj2 pvzI25) as K26r; move K26r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K33l; move K33l before pvzI26; pose proof (proj2 pvzI26) as K33r; move K33r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as K40l; move K40l before pvzI27; pose proof (proj2 pvzI27) as K40r; move K40r before pvzI27; clear pvzI27. pose proof (proj1 pvzI28) as K41l; move K41l before pvzI28; pose proof (proj2 pvzI28) as K41r; move K41r before pvzI28; clear pvzI28. pose proof (proj1 pvzI29) as K42l; move K42l before pvzI29; pose proof (proj2 pvzI29) as K42r; move K42r before pvzI29; clear pvzI29. pose proof (proj1 pvzI30) as K43l; move K43l before pvzI30; pose proof (proj2 pvzI30) as K43r; move K43r before pvzI30; clear pvzI30. pose proof (proj1 pvzI31) as K45l; move K45l before pvzI31; pose proof (proj2 pvzI31) as K45r; move K45r before pvzI31; clear pvzI31. pose proof (proj1 pvzI32) as K46l; move K46l before pvzI32; pose proof (proj2 pvzI32) as K46r; move K46r before pvzI32; clear pvzI32. pose proof (proj1 pvzI33) as K51l; move K51l before pvzI33; pose proof (proj2 pvzI33) as K51r; move K51r before pvzI33; clear pvzI33.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 41%nat => Z_to_bv 64 vz_41 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 41%nat => vz_41 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | 53%nat => vz_53 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 54%nat. }
  assert (HR: regs_ok E PazrF2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PazrF2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PazrF2.kn0).
  { unfold know_ok, PazrF2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52; lia | clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52; lia | clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52; lia | exactA K2]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52; lia | clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52; lia | clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K25 K32 K39 K53) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K25 K32 K39 K53) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K25 K32 K39 K53) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K25 K32 K39 K53) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 K25 K32 K39 K53; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K25 K32 K39 K53; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K25 K32 K39 K53; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K25 K32 K39 K53) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K25 K32 K39 K53) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K25 K32 K39 K53) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 K25 K32 K39 K53; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K25 K32 K39 K53; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K25 K32 K39 K53; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K25 K32 K39 K53) | evalEk ZA ltac:(clear - HV36l HV36r K17l K17r K46l K46r K51l K51r K49 K50 K52 K53 K54 K55 K56) | clear - HV33l HV33r K7l K7r K9 K11 K12 K25 K32 K39 K53; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K25 K32 K39 K53; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K25 K32 K39 K53) | evalEk ZA ltac:(clear - HV36l HV36r K17l K17r K46l K46r K51l K51r K49 K50 K52 K53 K54 K55 K56 HV37l HV37r K43l K43r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K25 K32 K39 K53; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K25 K32 K39 K53; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K25 K32 K39 K53) | evalEk ZA ltac:(clear - HV41l HV41r K45l K45r K46l K46r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K25 K32 K39 K53; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K25 K32 K39 K53; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K17l K17r K46l K46r K51l K51r K49 K50 K52 K53 K54 K55 K56) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K17l K17r K46l K46r K51l K51r K49 K50 K52 K53 K54 K55 K56) | clear; lia | exact K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K19l K19r K21 K24 K25 K54) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K19l K19r K21 K24 K25 K54) | clear; lia | exact K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K19l K19r K21 K24 K25 K54) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K19l K19r K21 K24 K25 K54) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K19l K19r K21 K24 K25 K54; lia | clear - HV34l HV34r K19l K19r K21 K24 K25 K54; lia | clear - HV34l HV34r K19l K19r K21 K24 K25 K54; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K19l K19r K21 K24 K25 K54) | evalEk ZA ltac:(clear - HV38l HV38r K40l K40r) | clear - HV34l HV34r K19l K19r K21 K24 K25 K54; lia | clear - HV34l HV34r K19l K19r K21 K24 K25 K54; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K19l K19r K21 K24 K25 K54) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K25 K32 K39 K53) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K19l K19r K21 K24 K25 K54) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K26l K26r K28 K31 K32 K55) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K26l K26r K28 K31 K32 K55) | clear; lia | exact K27]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K26l K26r K28 K31 K32 K55) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV35l HV35r K26l K26r K28 K31 K32 K55) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K26l K26r K28 K31 K32 K55; lia | clear - HV35l HV35r K26l K26r K28 K31 K32 K55; lia | clear - HV35l HV35r K26l K26r K28 K31 K32 K55; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV35l HV35r K26l K26r K28 K31 K32 K55) | evalEk ZA ltac:(clear - HV39l HV39r K41l K41r) | clear - HV35l HV35r K26l K26r K28 K31 K32 K55; lia | clear - HV35l HV35r K26l K26r K28 K31 K32 K55; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K26l K26r K28 K31 K32 K55) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K25 K32 K39 K53) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K26l K26r K28 K31 K32 K55) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV52l HV52r K33l K33r K35 K38 K39 K56) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV52l HV52r K33l K33r K35 K38 K39 K56) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV52l HV52r K33l K33r K35 K38 K39 K56) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV52l HV52r K33l K33r K35 K38 K39 K56) | evalEk ZA ltac:(clear) | clear - HV52l HV52r K33l K33r K35 K38 K39 K56; lia | clear - HV52l HV52r K33l K33r K35 K38 K39 K56; lia | clear - HV52l HV52r K33l K33r K35 K38 K39 K56; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV52l HV52r K33l K33r K35 K38 K39 K56) | evalEk ZA ltac:(clear - HV53l HV53r K42l K42r) | clear - HV52l HV52r K33l K33r K35 K38 K39 K56; lia | clear - HV52l HV52r K33l K33r K35 K38 K39 K56; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV52l HV52r K33l K33r K35 K38 K39 K56) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K25 K32 K39 K53) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV52l HV52r K33l K33r K35 K38 K39 K56) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K40l K40r) | exact (conj K40l K40r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r) | exact (conj K41l K41r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV53l HV53r K42l K42r) | exact (conj K42l K42r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K43l K43r K46l K46r K51l K51r K49 K50 K52 K53 K54 K55 K56) | exact (conj K43l K43r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K43l K43r K46l K46r K51l K51r K49 K50 K52 K53 K54 K55 K56) | clear; lia | exact K44]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K45l K45r K46l K46r) | exact (conj K45l K45r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K17l K17r K46l K46r K51l K51r K49 K50 K52 K53 K54 K55 K56 HV37l HV37r K43l K43r HV41l HV41r K45l K45r) | exact (conj K46l K46r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K17l K17r K46l K46r K51l K51r K49 K50 K52 K53 K54 K55 K56 HV37l HV37r K43l K43r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K17l K17r K46l K46r K51l K51r K49 K50 K52 K53 K54 K55 K56 HV37l HV37r K43l K43r; lia | clear - HV36l HV36r K17l K17r K46l K46r K51l K51r K49 K50 K52 K53 K54 K55 K56 HV37l HV37r K43l K43r; lia | clear - HV36l HV36r K17l K17r K46l K46r K51l K51r K49 K50 K52 K53 K54 K55 K56 HV37l HV37r K43l K43r; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K17l K17r K46l K46r K51l K51r K49 K50 K52 K53 K54 K55 K56 HV37l HV37r K43l K43r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K17l K17r K46l K46r K51l K51r K49 K50 K52 K53 K54 K55 K56 HV37l HV37r K43l K43r; lia | clear - HV36l HV36r K17l K17r K46l K46r K51l K51r K49 K50 K52 K53 K54 K55 K56 HV37l HV37r K43l K43r; lia | clear - HV36l HV36r K17l K17r K46l K46r K51l K51r K49 K50 K52 K53 K54 K55 K56 HV37l HV37r K43l K43r; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K17l K17r K46l K46r K51l K51r K49 K50 K52 K53 K54 K55 K56 HV37l HV37r K43l K43r) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K17l K17r K46l K46r K51l K51r K49 K50 K52 K53 K54 K55 K56 HV37l HV37r K43l K43r) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K17l K17r K46l K46r K51l K51r K49 K50 K52 K53 K54 K55 K56 HV37l HV37r K43l K43r) | exact (conj K51l K51r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K17l K17r K46l K46r K51l K51r K49 K50 K52 K53 K54 K55 K56 HV37l HV37r K43l K43r) | evalEk ZA ltac:(clear) | generalize K52; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K25 K32 K39 K53) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K17l K17r K46l K46r K51l K51r K49 K50 K52 K53 K54 K55 K56 HV37l HV37r K43l K43r) | evalEk ZA ltac:(clear) | generalize K53; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K19l K19r K21 K24 K25 K54) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K17l K17r K46l K46r K51l K51r K49 K50 K52 K53 K54 K55 K56 HV37l HV37r K43l K43r) | evalEk ZA ltac:(clear) | generalize K54; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K26l K26r K28 K31 K32 K55) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K17l K17r K46l K46r K51l K51r K49 K50 K52 K53 K54 K55 K56 HV37l HV37r K43l K43r) | evalEk ZA ltac:(clear) | generalize K55; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV52l HV52r K33l K33r K35 K38 K39 K56) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K17l K17r K46l K46r K51l K51r K49 K50 K52 K53 K54 K55 K56 HV37l HV37r K43l K43r) | evalEk ZA ltac:(clear) | generalize K56; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52; lia | clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52; lia | exactA K57]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52; lia | clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52; lia | exactA K58]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52; lia | clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52; lia | exactA K59]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52; lia | clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52; lia | exactA K60]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52; lia | clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52; lia | exactA K61]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52) | evalEk ZA ltac:(clear - HV36l HV36r K17l K17r K46l K46r K51l K51r K49 K50 K52 K53 K54 K55 K56 HV37l HV37r K43l K43r) | clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52; lia | clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52; lia | exactA K62]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52) | evalEk ZA ltac:(clear - HV36l HV36r K17l K17r K46l K46r K51l K51r K49 K50 K52 K53 K54 K55 K56 HV37l HV37r K43l K43r) | clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52; lia | clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52; lia | exactA K63]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K25 K32 K39 K53) | clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52; lia | clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52; lia | exactA K64]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52; lia | clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52; lia | exactA K65]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52) | evalEk ZA ltac:(clear - HV52l HV52r K33l K33r K35 K38 K39 K56) | clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52; lia | clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52; lia | exactA K66]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PazrF2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PazrF2.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((vz_36 + vz_37) + 0) <= bv_unsigned a < ((vz_36 + vz_37) + 0) + 40) -> ~ ((vz_33 + 8) <= bv_unsigned a < (vz_33 + 8) + 8) -> ~ ((vz_2 - 128) <= bv_unsigned a < (vz_2 - 128) + 128) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PazrF2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r K46l K46r K51l K51r K49 K50 K52 K53 K54 K55 K56 HV37l HV37r K43l K43r) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K17l K17r K46l K46r K51l K51r K49 K50 K52 K53 K54 K55 K56 HV37l HV37r K43l K43r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K25 K32 K39 K53) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 K25 K32 K39 K53 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K24 K31 K38 K52 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PazrF2.ps0) with 0xad09c in Hms. change (SR.ps_regs PazrF2.ps0) with (map (fun i => (i, nth i PazrF2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PazrF2.ps0) with PazrF2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PazrF2.regs0 PazrF2.regs_out0 60 KS_azrF2 KS_azrF2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PazrF2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PazrF2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrF2.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PazrF2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrF2.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PazrF2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrF2.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PazrF2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrF2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PazrF2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrF2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PazrF2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrF2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PazrF2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrF2.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PazrF2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrF2.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PazrF2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrF2.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PazrF2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrF2.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PazrF2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrF2.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PazrF2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrF2.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PazrF2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrF2.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PazrF2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrF2.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PazrF2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazrF2.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PazrF2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K25 K32 K39 K53) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r K46l K46r K51l K51r K49 K50 K52 K53 K54 K55 K56 HV37l HV37r K43l K43r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r K46l K46r K51l K51r K49 K50 K52 K53 K54 K55 K56 HV37l HV37r K43l K43r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r K46l K46r K51l K51r K49 K50 K52 K53 K54 K55 K56 HV37l HV37r K43l K43r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r K46l K46r K51l K51r K49 K50 K52 K53 K54 K55 K56 HV37l HV37r K43l K43r) | evalEk' ZA Hag ltac:(clear - HV53l HV53r K42l K42r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r K46l K46r K51l K51r K49 K50 K52 K53 K54 K55 K56 HV37l HV37r K43l K43r) | evalEk' ZA Hag ltac:(clear - HV39l HV39r K41l K41r) | clear; lia]. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r K46l K46r K51l K51r K49 K50 K52 K53 K54 K55 K56 HV37l HV37r K43l K43r) | evalEk' ZA Hag ltac:(clear - HV38l HV38r K40l K40r) | clear; lia].
Qed.
(* [comment removed for export] *)

End PNAERP.
