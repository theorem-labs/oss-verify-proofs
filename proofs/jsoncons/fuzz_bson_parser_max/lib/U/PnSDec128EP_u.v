(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.seg Require LibSegBs_dkC1_u LibSegBs_dkC20_u LibSegBs_dkC2c_u LibSegBs_dkC30_u LibSegBs_dkC3c_u LibSegBs_dkA2_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNSDEP.
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
Module PdkC1 := LibSegBs_dkC1_u.
Definition KS_dkC1 : list nat := Eval vm_compute in (BG.kept_list 80 PdkC1.regs0 PdkC1.regs_out0).
Lemma KS_dkC1_ok : BG.kept_ok 80 PdkC1.regs0 PdkC1.regs_out0 KS_dkC1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dkC1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 ((V 33%nat) + 42) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) ->
  140735332483312 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 240) 240 -> 4096 <= (V 33%nat) <= 140737488355286 ->
  L5.writable RSEGS M (V 33%nat) 42 -> (((V 2%nat) - 336) + 336 <= (V 33%nat) \/ (V 33%nat) + 42 <= ((V 2%nat) - 336)) -> ((V 33%nat) + 42 <= 65536 \/ 65536 + 897024 <= (V 33%nat)) -> 4096 <= (V 35%nat) <= 140737488355312 ->
  aligned (V 35%nat) 8 -> L5.u64_at RSEGS M (V 35%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 35%nat) + 8) (V 37%nat) -> (((V 2%nat) - 240) + 240 <= (V 35%nat) \/ (V 35%nat) + 16 <= ((V 2%nat) - 240)) ->
  ((V 33%nat) + 42 <= (V 35%nat) \/ (V 35%nat) + 16 <= (V 33%nat)) -> L5.img_clear M 65536 754672 -> L5.img_clear M 820640 820648 -> L5.writable RSEGS M 820640 8 ->
  L5.img_clear M 820672 820680 -> L5.writable RSEGS M 820672 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 240) <= bv_unsigned a < ((V 2%nat) - 240) + 240) -> ~ ((0 + 820640) <= bv_unsigned a < (0 + 820640) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 240) <= i < ((V 2%nat) - 240) + 240) -> ~ ((0 + 820640) <= i < (0 + 820640) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x38a78 M) (st fx' R' 0x37f44 M')
        /\ (forall x, In x KS_dkC1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 233924
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 256)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 42)
        /\ getr R' (reg 10) = Z_to_bv 64 820616
        /\ getr R' (reg 11) = Z_to_bv 64 78319
        /\ getr R' (reg 12) = Z_to_bv 64 2
        /\ getr R' (reg 18) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 35%nat)
        /\ L5.u8_at RSEGS M' 820641 2
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G10 G11 G12 pvzI6 K1 K2 pvzI7 K4 K5 K6 pvzI8 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K7l; move K7l before pvzI8; pose proof (proj2 pvzI8) as K7r; move K7r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PdkC1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdkC1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdkC1.kn0).
  { unfold know_ok, PdkC1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K11) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K11) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K11; lia | clear - HV2l HV2r K0l K0r K5 K11; lia | clear - HV2l HV2r K0l K0r K5 K11; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K6 K12) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K6 K12) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5 K6 K12; lia | clear - HV33l HV33r K3l K3r K5 K6 K12; lia | clear - HV33l HV33r K3l K3r K5 K6 K12; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K6 K12) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K6 K12) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K7l K7r K11 K12) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K7l K7r K11 K12) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K7l K7r K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV35l HV35r K7l K7r K11 K12; lia | clear - HV35l HV35r K7l K7r K11 K12; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K7l K7r K11 K12) | evalEk ZA ltac:(clear - HV37l HV37r) | clear - HV35l HV35r K7l K7r K11 K12; lia | clear - HV35l HV35r K7l K7r K11 K12; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K7l K7r K11 K12) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K6 K12) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K7l K7r K11 K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K17]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PdkC1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PdkC1.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 240) <= bv_unsigned a < (vz_2 - 240) + 240) -> ~ ((0 + 820640) <= bv_unsigned a < (0 + 820640) + 2) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PdkC1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K11 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PdkC1.ps0) with 0x37f44 in Hms. change (SR.ps_regs PdkC1.ps0) with (map (fun i => (i, nth i PdkC1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PdkC1.ps0) with PdkC1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkC1.regs0 PdkC1.regs_out0 80 KS_dkC1 KS_dkC1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PdkC1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PdkC1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkC1.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PdkC1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkC1.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PdkC1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkC1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PdkC1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkC1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PdkC1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkC1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PdkC1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkC1.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PdkC1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkC1.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PdkC1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PdkC20 := LibSegBs_dkC20_u.
Definition KS_dkC20 : list nat := Eval vm_compute in (BG.kept_list 80 PdkC20.regs0 PdkC20.regs_out0).
Lemma KS_dkC20_ok : BG.kept_ok 80 PdkC20.regs0 PdkC20.regs_out0 KS_dkC20 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dkC20_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 42) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 19) = Z_to_bv 64 (V 35%nat) ->
  140735332483408 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 336) 336 -> L5.img_clear M 65536 754672 ->
  L5.img_clear M 959059 959060 -> L5.img_clear M 958472 958480 -> L5.u32_at RSEGS M 958480 1 -> L5.img_clear M 958484 958488 ->
  L5.u64_at RSEGS M 958488 958496 -> L5.img_clear M 958496 958504 -> L5.writable RSEGS M 958472 544 -> L5.img_clear M 958512 958760 ->
  L5.img_clear M 958768 959016 -> L5.img_clear M 820672 820680 -> L5.writable RSEGS M 820672 8 -> L5.writable RSEGS M 820640 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 336) <= bv_unsigned a < ((V 2%nat) - 336) + 96) -> ~ ((0 + 820640) <= bv_unsigned a < (0 + 820640) + 2) -> ~ ((0 + 820672) <= bv_unsigned a < (0 + 820672) + 2) -> ~ ((0 + 958480) <= bv_unsigned a < (0 + 958480) + 4) -> ~ ((0 + 958488) <= bv_unsigned a < (0 + 958488) + 8) -> ~ ((0 + 958512) <= bv_unsigned a < (0 + 958512) + 8) -> ~ ((0 + 958768) <= bv_unsigned a < (0 + 958768) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 336) <= i < ((V 2%nat) - 336) + 96) -> ~ ((0 + 820640) <= i < (0 + 820640) + 2) -> ~ ((0 + 820672) <= i < (0 + 820672) + 2) -> ~ ((0 + 958480) <= i < (0 + 958480) + 4) -> ~ ((0 + 958488) <= i < (0 + 958488) + 8) -> ~ ((0 + 958512) <= i < (0 + 958512) + 8) -> ~ ((0 + 958768) <= i < (0 + 958768) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x391c4 M) (st fx' R' 0x37f44 M')
        /\ (forall x, In x KS_dkC20 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 234008
        /\ getr R' (reg 10) = Z_to_bv 64 820648
        /\ getr R' (reg 11) = Z_to_bv 64 73575
        /\ getr R' (reg 12) = Z_to_bv 64 2
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ L5.u8_at RSEGS M' 820673 2
        /\ L5.u8_at RSEGS M' 820641 1
        /\ L5.u8_at RSEGS M' 820640 1
        /\ L5.u32_at RSEGS M' 958480 2
        /\ L5.u64_at RSEGS M' 958768 820616
        /\ L5.u64_at RSEGS M' 958512 361520
        /\ L5.u64_at RSEGS M' 958488 958496).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G8 G18 G19 pvzI4 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 36%nat. }
  assert (HR: regs_ok E PdkC20.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdkC20.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdkC20.kn0).
  { unfold know_ok, PdkC20.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K11]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K15]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PdkC20.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PdkC20.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 336) <= bv_unsigned a < (vz_2 - 336) + 96) -> ~ ((0 + 820640) <= bv_unsigned a < (0 + 820640) + 2) -> ~ ((0 + 820672) <= bv_unsigned a < (0 + 820672) + 2) -> ~ ((0 + 958480) <= bv_unsigned a < (0 + 958480) + 4) -> ~ ((0 + 958488) <= bv_unsigned a < (0 + 958488) + 8) -> ~ ((0 + 958512) <= bv_unsigned a < (0 + 958512) + 8) -> ~ ((0 + 958768) <= bv_unsigned a < (0 + 958768) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6. apply Hfr. unfold PdkC20.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn3; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn4; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn5; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn6; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PdkC20.ps0) with 0x37f44 in Hms. change (SR.ps_regs PdkC20.ps0) with (map (fun i => (i, nth i PdkC20.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PdkC20.ps0) with PdkC20.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkC20.regs0 PdkC20.regs_out0 80 KS_dkC20 KS_dkC20_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PdkC20.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PdkC20.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkC20.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PdkC20.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkC20.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PdkC20.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkC20.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PdkC20.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkC20.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PdkC20.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PdkC2c := LibSegBs_dkC2c_u.
Definition KS_dkC2c : list nat := Eval vm_compute in (BG.kept_list 80 PdkC2c.regs0 PdkC2c.regs_out0).
Lemma KS_dkC2c_ok : BG.kept_ok 80 PdkC2c.regs0 PdkC2c.regs_out0 KS_dkC2c = true. Proof. vm_compute. reflexivity. Qed.
Lemma dkC2c_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 42) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 19) = Z_to_bv 64 (V 35%nat) ->
  140735332483408 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 336) 336 -> L5.img_clear M 65536 754672 ->
  L5.img_clear M 959059 959060 -> L5.img_clear M 958472 958480 -> L5.u32_at RSEGS M 958480 2 -> L5.img_clear M 958484 958488 ->
  L5.u64_at RSEGS M 958488 958496 -> L5.img_clear M 958496 958504 -> L5.writable RSEGS M 958472 544 -> L5.img_clear M 958520 958760 ->
  L5.img_clear M 958776 959016 -> L5.img_clear M 820672 820680 -> L5.writable RSEGS M 820672 8 -> L5.writable RSEGS M 820640 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 336) <= bv_unsigned a < ((V 2%nat) - 336) + 96) -> ~ ((0 + 820640) <= bv_unsigned a < (0 + 820640) + 2) -> ~ ((0 + 820672) <= bv_unsigned a < (0 + 820672) + 2) -> ~ ((0 + 958480) <= bv_unsigned a < (0 + 958480) + 4) -> ~ ((0 + 958488) <= bv_unsigned a < (0 + 958488) + 8) -> ~ ((0 + 958520) <= bv_unsigned a < (0 + 958520) + 8) -> ~ ((0 + 958776) <= bv_unsigned a < (0 + 958776) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 336) <= i < ((V 2%nat) - 336) + 96) -> ~ ((0 + 820640) <= i < (0 + 820640) + 2) -> ~ ((0 + 820672) <= i < (0 + 820672) + 2) -> ~ ((0 + 958480) <= i < (0 + 958480) + 4) -> ~ ((0 + 958488) <= i < (0 + 958488) + 8) -> ~ ((0 + 958520) <= i < (0 + 958520) + 8) -> ~ ((0 + 958776) <= i < (0 + 958776) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x391c4 M) (st fx' R' 0x37f44 M')
        /\ (forall x, In x KS_dkC2c -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 234008
        /\ getr R' (reg 10) = Z_to_bv 64 820648
        /\ getr R' (reg 11) = Z_to_bv 64 73575
        /\ getr R' (reg 12) = Z_to_bv 64 2
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ L5.u8_at RSEGS M' 820673 2
        /\ L5.u8_at RSEGS M' 820641 1
        /\ L5.u8_at RSEGS M' 820640 1
        /\ L5.u32_at RSEGS M' 958480 3
        /\ L5.u64_at RSEGS M' 958776 820616
        /\ L5.u64_at RSEGS M' 958520 361520
        /\ L5.u64_at RSEGS M' 958488 958496).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G8 G18 G19 pvzI4 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 36%nat. }
  assert (HR: regs_ok E PdkC2c.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdkC2c.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdkC2c.kn0).
  { unfold know_ok, PdkC2c.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K11]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K15]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PdkC2c.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PdkC2c.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 336) <= bv_unsigned a < (vz_2 - 336) + 96) -> ~ ((0 + 820640) <= bv_unsigned a < (0 + 820640) + 2) -> ~ ((0 + 820672) <= bv_unsigned a < (0 + 820672) + 2) -> ~ ((0 + 958480) <= bv_unsigned a < (0 + 958480) + 4) -> ~ ((0 + 958488) <= bv_unsigned a < (0 + 958488) + 8) -> ~ ((0 + 958520) <= bv_unsigned a < (0 + 958520) + 8) -> ~ ((0 + 958776) <= bv_unsigned a < (0 + 958776) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6. apply Hfr. unfold PdkC2c.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn3; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn4; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn5; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn6; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PdkC2c.ps0) with 0x37f44 in Hms. change (SR.ps_regs PdkC2c.ps0) with (map (fun i => (i, nth i PdkC2c.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PdkC2c.ps0) with PdkC2c.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkC2c.regs0 PdkC2c.regs_out0 80 KS_dkC2c KS_dkC2c_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PdkC2c.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PdkC2c.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkC2c.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PdkC2c.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkC2c.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PdkC2c.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkC2c.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PdkC2c.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkC2c.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PdkC2c.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PdkC30 := LibSegBs_dkC30_u.
Definition KS_dkC30 : list nat := Eval vm_compute in (BG.kept_list 80 PdkC30.regs0 PdkC30.regs_out0).
Lemma KS_dkC30_ok : BG.kept_ok 80 PdkC30.regs0 PdkC30.regs_out0 KS_dkC30 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dkC30_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 42) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 19) = Z_to_bv 64 (V 35%nat) ->
  140735332483408 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 336) 336 -> L5.img_clear M 65536 754672 ->
  L5.img_clear M 959059 959060 -> L5.img_clear M 958472 958480 -> L5.u32_at RSEGS M 958480 2 -> L5.img_clear M 958484 958488 ->
  L5.u64_at RSEGS M 958488 958496 -> L5.img_clear M 958496 958504 -> L5.writable RSEGS M 958472 544 -> L5.img_clear M 958520 958760 ->
  L5.img_clear M 958776 959016 -> L5.writable RSEGS M 820672 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 336) <= bv_unsigned a < ((V 2%nat) - 336) + 96) -> ~ ((0 + 820672) <= bv_unsigned a < (0 + 820672) + 2) -> ~ ((0 + 958480) <= bv_unsigned a < (0 + 958480) + 4) -> ~ ((0 + 958488) <= bv_unsigned a < (0 + 958488) + 8) -> ~ ((0 + 958520) <= bv_unsigned a < (0 + 958520) + 8) -> ~ ((0 + 958776) <= bv_unsigned a < (0 + 958776) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 336) <= i < ((V 2%nat) - 336) + 96) -> ~ ((0 + 820672) <= i < (0 + 820672) + 2) -> ~ ((0 + 958480) <= i < (0 + 958480) + 4) -> ~ ((0 + 958488) <= i < (0 + 958488) + 8) -> ~ ((0 + 958520) <= i < (0 + 958520) + 8) -> ~ ((0 + 958776) <= i < (0 + 958776) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x39218 M) (st fx' R' 0x38acc M')
        /\ (forall x, In x KS_dkC30 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 234048
        /\ getr R' (reg 10) = Z_to_bv 64 820672
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 16
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ L5.u8_at RSEGS M' 820673 1
        /\ L5.u8_at RSEGS M' 820672 1
        /\ L5.u32_at RSEGS M' 958480 3
        /\ L5.u64_at RSEGS M' 958776 820648
        /\ L5.u64_at RSEGS M' 958520 361520
        /\ L5.u64_at RSEGS M' 958488 958496).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G8 G18 G19 pvzI4 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 36%nat. }
  assert (HR: regs_ok E PdkC30.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdkC30.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdkC30.kn0).
  { unfold know_ok, PdkC30.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K11]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K13]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PdkC30.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PdkC30.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 336) <= bv_unsigned a < (vz_2 - 336) + 96) -> ~ ((0 + 820672) <= bv_unsigned a < (0 + 820672) + 2) -> ~ ((0 + 958480) <= bv_unsigned a < (0 + 958480) + 4) -> ~ ((0 + 958488) <= bv_unsigned a < (0 + 958488) + 8) -> ~ ((0 + 958520) <= bv_unsigned a < (0 + 958520) + 8) -> ~ ((0 + 958776) <= bv_unsigned a < (0 + 958776) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3 Hn4 Hn5. apply Hfr. unfold PdkC30.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn3; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn4; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn5; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3 Hn4 Hn5. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PdkC30.ps0) with 0x38acc in Hms. change (SR.ps_regs PdkC30.ps0) with (map (fun i => (i, nth i PdkC30.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PdkC30.ps0) with PdkC30.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkC30.regs0 PdkC30.regs_out0 80 KS_dkC30 KS_dkC30_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PdkC30.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PdkC30.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkC30.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PdkC30.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkC30.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PdkC30.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkC30.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PdkC30.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkC30.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PdkC30.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PdkC3c := LibSegBs_dkC3c_u.
Definition KS_dkC3c : list nat := Eval vm_compute in (BG.kept_list 80 PdkC3c.regs0 PdkC3c.regs_out0).
Lemma KS_dkC3c_ok : BG.kept_ok 80 PdkC3c.regs0 PdkC3c.regs_out0 KS_dkC3c = true. Proof. vm_compute. reflexivity. Qed.
Lemma dkC3c_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 42) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 19) = Z_to_bv 64 (V 35%nat) ->
  140735332483408 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 336) 336 -> L5.img_clear M 65536 754672 ->
  L5.img_clear M 959059 959060 -> L5.img_clear M 958472 958480 -> L5.u32_at RSEGS M 958480 3 -> L5.img_clear M 958484 958488 ->
  L5.u64_at RSEGS M 958488 958496 -> L5.img_clear M 958496 958504 -> L5.writable RSEGS M 958472 544 -> L5.img_clear M 958528 958760 ->
  L5.img_clear M 958784 959016 -> L5.writable RSEGS M 820672 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 336) <= bv_unsigned a < ((V 2%nat) - 336) + 96) -> ~ ((0 + 820672) <= bv_unsigned a < (0 + 820672) + 2) -> ~ ((0 + 958480) <= bv_unsigned a < (0 + 958480) + 4) -> ~ ((0 + 958488) <= bv_unsigned a < (0 + 958488) + 8) -> ~ ((0 + 958528) <= bv_unsigned a < (0 + 958528) + 8) -> ~ ((0 + 958784) <= bv_unsigned a < (0 + 958784) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 336) <= i < ((V 2%nat) - 336) + 96) -> ~ ((0 + 820672) <= i < (0 + 820672) + 2) -> ~ ((0 + 958480) <= i < (0 + 958480) + 4) -> ~ ((0 + 958488) <= i < (0 + 958488) + 8) -> ~ ((0 + 958528) <= i < (0 + 958528) + 8) -> ~ ((0 + 958784) <= i < (0 + 958784) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x39218 M) (st fx' R' 0x38acc M')
        /\ (forall x, In x KS_dkC3c -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 234048
        /\ getr R' (reg 10) = Z_to_bv 64 820672
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 24
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ L5.u8_at RSEGS M' 820673 1
        /\ L5.u8_at RSEGS M' 820672 1
        /\ L5.u32_at RSEGS M' 958480 4
        /\ L5.u64_at RSEGS M' 958784 820648
        /\ L5.u64_at RSEGS M' 958528 361520
        /\ L5.u64_at RSEGS M' 958488 958496).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G8 G18 G19 pvzI4 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 36%nat. }
  assert (HR: regs_ok E PdkC3c.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdkC3c.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdkC3c.kn0).
  { unfold know_ok, PdkC3c.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K11]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K13]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PdkC3c.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PdkC3c.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 336) <= bv_unsigned a < (vz_2 - 336) + 96) -> ~ ((0 + 820672) <= bv_unsigned a < (0 + 820672) + 2) -> ~ ((0 + 958480) <= bv_unsigned a < (0 + 958480) + 4) -> ~ ((0 + 958488) <= bv_unsigned a < (0 + 958488) + 8) -> ~ ((0 + 958528) <= bv_unsigned a < (0 + 958528) + 8) -> ~ ((0 + 958784) <= bv_unsigned a < (0 + 958784) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3 Hn4 Hn5. apply Hfr. unfold PdkC3c.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn3; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn4; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn5; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3 Hn4 Hn5. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PdkC3c.ps0) with 0x38acc in Hms. change (SR.ps_regs PdkC3c.ps0) with (map (fun i => (i, nth i PdkC3c.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PdkC3c.ps0) with PdkC3c.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkC3c.regs0 PdkC3c.regs_out0 80 KS_dkC3c KS_dkC3c_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PdkC3c.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PdkC3c.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkC3c.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PdkC3c.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkC3c.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PdkC3c.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkC3c.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PdkC3c.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdkC3c.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PdkC3c.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PdkA2 := LibSegBs_dkA2_u.
Definition KS_dkA2_0 : list nat := Eval vm_compute in (BG.kept_list 80 PdkA2.regs0 PdkA2.regs_out0).
Lemma KS_dkA2_0_ok : BG.kept_ok 80 PdkA2.regs0 PdkA2.regs_out0 KS_dkA2_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_dkA2_1 : list nat := Eval vm_compute in (BG.kept_list 80 PdkA2.regs0 PdkA2.regs_out1).
Lemma KS_dkA2_1_ok : BG.kept_ok 80 PdkA2.regs0 PdkA2.regs_out1 KS_dkA2_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma dkA2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 42) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 19) = Z_to_bv 64 (V 35%nat) ->
  140735332483312 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 240) 240 -> 4096 <= (V 33%nat) <= 140737488355286 ->
  L5.writable RSEGS M (V 33%nat) 42 -> (((V 2%nat) - 336) + 336 <= (V 33%nat) \/ (V 33%nat) + 42 <= ((V 2%nat) - 336)) -> ((V 33%nat) + 42 <= 65536 \/ 65536 + 897024 <= (V 33%nat)) -> 4096 <= (V 35%nat) <= 140737488355312 ->
  aligned (V 35%nat) 8 -> L5.u64_at RSEGS M (V 35%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 35%nat) + 8) (V 37%nat) -> (((V 2%nat) - 240) + 240 <= (V 35%nat) \/ (V 35%nat) + 16 <= ((V 2%nat) - 240)) ->
  ((V 33%nat) + 42 <= (V 35%nat) \/ (V 35%nat) + 16 <= (V 33%nat)) -> L5.img_clear M 65536 754672 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 216) <= bv_unsigned a < ((V 2%nat) - 216) + 144) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 216) <= i < ((V 2%nat) - 216) + 144) -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x38acc M) (st fx' R' 0x38afc M')
        /\ (forall x, In x KS_dkA2_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 9) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EVar 37) (ELit 0))) <= 0
        /\ L5KA.zeros_at M' ((V 2%nat) - 216) 144)
      \/ (msteps RSEGS (st fx R 0x38acc M) (st fx' R' 0x38afc M')
        /\ (forall x, In x KS_dkA2_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 10) = Z_to_bv 64 45
        /\ L5.u8_at RSEGS M' (V 33%nat) 45
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EVar 37) (ELit 0))) <= 1
        /\ L5KA.zeros_at M' ((V 2%nat) - 216) 144)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G18 G19 pvzI6 K1 K2 pvzI7 K4 K5 K6 pvzI8 K8 K9 K10 K11 K12 K13.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K7l; move K7l before pvzI8; pose proof (proj2 pvzI8) as K7r; move K7r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PdkA2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdkA2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdkA2.kn0).
  { unfold know_ok, PdkA2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K11) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K11) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K11; lia | clear - HV2l HV2r K0l K0r K5 K11; lia | clear - HV2l HV2r K0l K0r K5 K11; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K6 K12) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K6 K12) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5 K6 K12; lia | clear - HV33l HV33r K3l K3r K5 K6 K12; lia | clear - HV33l HV33r K3l K3r K5 K6 K12; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K6 K12) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K6 K12) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K7l K7r K11 K12) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K7l K7r K11 K12) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K7l K7r K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV35l HV35r K7l K7r K11 K12; lia | clear - HV35l HV35r K7l K7r K11 K12; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K7l K7r K11 K12) | evalEk ZA ltac:(clear - HV37l HV37r) | clear - HV35l HV35r K7l K7r K11 K12; lia | clear - HV35l HV35r K7l K7r K11 K12; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K7l K7r K11 K12) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K6 K12) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K7l K7r K11 K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K13]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PdkA2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PdkA2.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 216) <= bv_unsigned a < (vz_2 - 216) + 144) -> ~ ((vz_33 + 0) <= bv_unsigned a < (vz_33 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PdkA2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K11 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5 K6 K12) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K3l K3r K5 K6 K12 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PdkA2.ps0) with 0x38afc in Hms. change (SR.ps_regs PdkA2.ps0) with (map (fun i => (i, nth i PdkA2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PdkA2.ps0) with PdkA2.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkA2.regs0 PdkA2.regs_out0 80 KS_dkA2_0 KS_dkA2_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PdkA2.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PdkA2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkA2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PdkA2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    eapply zeros_of_KZeroa; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
  - right.
    change (SR.ps_pc PdkA2.ps1) with 0x38afc in Hms. change (SR.ps_regs PdkA2.ps1) with (map (fun i => (i, nth i PdkA2.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PdkA2.ps1) with PdkA2.cells1 in Hcells. unfold PdkA2.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PdkA2.regs0 PdkA2.regs_out1 80 KS_dkA2_1 KS_dkA2_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PdkA2.regs_out1 E' R' 9 Hregs) by (clear; lia). cbn [nth PdkA2.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PdkA2.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PdkA2.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5 K6 K12) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    eapply zeros_of_KZeroa; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

End PNSDEP.
