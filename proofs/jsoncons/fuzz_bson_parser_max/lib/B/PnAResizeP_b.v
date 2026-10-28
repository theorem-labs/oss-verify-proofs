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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require LibSegBa_arzS_b LibSegBa_arzL_b LibSegBa_arzTS_b LibSegBa_arzTL_b LibSegBa_aapS0_b LibSegBa_aapL0_b LibSegBa_afitS_b LibSegBa_afitL_b LibSegBa_aapMS_b LibSegBa_aapML_b LibSegBa_agrowS_b LibSegBa_agrowL_b LibSegBa_arec_b LibSegBa_apN_b LibSegBa_apDS_b LibSegBa_apDL_b LibSegBa_apF_b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PMARZP.
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
Module ParzS := LibSegBa_arzS_b.
Definition KS_arzS_0 : list nat := Eval vm_compute in (BG.kept_list 48 ParzS.regs0 ParzS.regs_out0).
Lemma KS_arzS_0_ok : BG.kept_ok 48 ParzS.regs0 ParzS.regs_out0 KS_arzS_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_arzS_1 : list nat := Eval vm_compute in (BG.kept_list 48 ParzS.regs0 ParzS.regs_out1).
Lemma KS_arzS_1_ok : BG.kept_ok 48 ParzS.regs0 ParzS.regs_out1 KS_arzS_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma arzS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 11) = Z_to_bv 64 (V 37%nat) ->
  6905856 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 -> aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 -> L5.u8_at RSEGS M (bv_unsigned (getr R (reg 10))) (V 33%nat) ->
  0 <= (V 33%nat) <= 44 -> Z.testbit (V 33%nat) 0 = false -> 0 <= (V 37%nat) <= 67125248 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd628c M) (st fx' R' 0xd62a0 M')
        /\ (forall x, In x KS_arzS_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 33%nat) / 2)
        /\ (V 37%nat) <= ((V 33%nat) / 2))
      \/ (msteps RSEGS (st fx R 0xd628c M) (st fx' R' 0xd5d10 M')
        /\ (forall x, In x KS_arzS_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 37%nat) - ((V 33%nat) / 2))
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 33%nat) / 2)
        /\ ((V 33%nat) / 2) < (V 37%nat))).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G11 pvzI4 K1 K2 K3 pvzI5 K5 pvzI6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K4l; move K4l before pvzI5; pose proof (proj2 pvzI5) as K4r; move K4r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K6l; move K6l before pvzI6; pose proof (proj2 pvzI6) as K6r; move K6r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E ParzS.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParzS.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParzS.kn0).
  { unfold know_ok, ParzS.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K0l K0r) | evalEk ZA ltac:(clear) | clear - K0l K0r; lia | clear - K0l K0r; lia | clear - K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - K0l K0r) | evalEk ZA ltac:(clear - HV33l HV33r K4l K4r K5) | clear - K0l K0r; lia | clear - K0l K0r; lia | byte_tac ltac:(clear - HV33l HV33r K4l K4r K5) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K4l K4r K5) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K4l K4r K5) | clear; lia | rewrite (L5K.land1_bit0_false vz_33 ltac:(clear - HV33l HV33r K4l K4r K5; lia) K5); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (ParzS.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParzS.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold ParzS.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc ParzS.ps0) with 0xd62a0 in Hms. change (SR.ps_regs ParzS.ps0) with (map (fun i => (i, nth i ParzS.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells ParzS.ps0) with ParzS.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' ParzS.regs0 ParzS.regs_out0 48 KS_arzS_0 KS_arzS_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg ParzS.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth ParzS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParzS.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth ParzS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  - right.
    change (SR.ps_pc ParzS.ps1) with 0xd5d10 in Hms. change (SR.ps_regs ParzS.ps1) with (map (fun i => (i, nth i ParzS.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells ParzS.ps1) with ParzS.cells1 in Hcells. unfold ParzS.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' ParzS.regs0 ParzS.regs_out1 48 KS_arzS_1 KS_arzS_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg ParzS.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth ParzS.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParzS.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth ParzS.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParzS.regs_out1 E' R' 14 Hregs) by (clear; lia). cbn [nth ParzS.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module ParzL := LibSegBa_arzL_b.
Definition KS_arzL_0 : list nat := Eval vm_compute in (BG.kept_list 48 ParzL.regs0 ParzL.regs_out0).
Lemma KS_arzL_0_ok : BG.kept_ok 48 ParzL.regs0 ParzL.regs_out0 KS_arzL_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_arzL_1 : list nat := Eval vm_compute in (BG.kept_list 48 ParzL.regs0 ParzL.regs_out1).
Lemma KS_arzL_1_ok : BG.kept_ok 48 ParzL.regs0 ParzL.regs_out1 KS_arzL_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma arzL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 11) = Z_to_bv 64 (V 37%nat) ->
  6905856 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 -> aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 -> L5.u8_at RSEGS M (bv_unsigned (getr R (reg 10))) (V 33%nat) ->
  0 <= (V 33%nat) <= 255 -> Z.testbit (V 33%nat) 0 = true -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 34%nat) -> 0 <= (V 34%nat) <= 134217728 ->
  0 <= (V 37%nat) <= 67125248 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd628c M) (st fx' R' 0xd5d10 M')
        /\ (forall x, In x KS_arzL_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 (((-1) * (V 34%nat)) + (V 37%nat))
        /\ getr R' (reg 13) = Z_to_bv 64 1
        /\ getr R' (reg 14) = Z_to_bv 64 (V 34%nat)
        /\ (V 34%nat) < (V 37%nat))
      \/ (msteps RSEGS (st fx R 0xd628c M) (st fx' R' 0xd62a0 M')
        /\ (forall x, In x KS_arzL_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 13) = Z_to_bv 64 1
        /\ getr R' (reg 14) = Z_to_bv 64 (V 34%nat)
        /\ (V 37%nat) <= (V 34%nat))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G11 pvzI5 K1 K2 K3 pvzI6 K5 K6 pvzI7 pvzI8.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K4l; move K4l before pvzI6; pose proof (proj2 pvzI6) as K4r; move K4r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K7l; move K7l before pvzI7; pose proof (proj2 pvzI7) as K7r; move K7r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K8l; move K8l before pvzI8; pose proof (proj2 pvzI8) as K8r; move K8r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E ParzL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParzL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParzL.kn0).
  { unfold know_ok, ParzL.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K0l K0r) | evalEk ZA ltac:(clear) | clear - K0l K0r; lia | clear - K0l K0r; lia | clear - K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - K0l K0r) | evalEk ZA ltac:(clear - HV33l HV33r K4l K4r K5) | clear - K0l K0r; lia | clear - K0l K0r; lia | byte_tac ltac:(clear - HV33l HV33r K4l K4r K5) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K4l K4r K5) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K4l K4r K5) | clear; lia | rewrite (L5K.land1_bit0_true vz_33 ltac:(clear - HV33l HV33r K4l K4r K5; lia) K5); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K0l K0r) | evalEk ZA ltac:(clear - HV34l HV34r K7l K7r) | clear - K0l K0r; lia | clear - K0l K0r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (ParzL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParzL.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold ParzL.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc ParzL.ps0) with 0xd5d10 in Hms. change (SR.ps_regs ParzL.ps0) with (map (fun i => (i, nth i ParzL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells ParzL.ps0) with ParzL.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' ParzL.regs0 ParzL.regs_out0 48 KS_arzL_0 KS_arzL_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg ParzL.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParzL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParzL.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth ParzL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParzL.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth ParzL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  - right.
    change (SR.ps_pc ParzL.ps1) with 0xd62a0 in Hms. change (SR.ps_regs ParzL.ps1) with (map (fun i => (i, nth i ParzL.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells ParzL.ps1) with ParzL.cells1 in Hcells. unfold ParzL.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' ParzL.regs0 ParzL.regs_out1 48 KS_arzL_1 KS_arzL_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg ParzL.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth ParzL.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParzL.regs_out1 E' R' 14 Hregs) by (clear; lia). cbn [nth ParzL.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module ParzTS := LibSegBa_arzTS_b.
Definition KS_arzTS : list nat := Eval vm_compute in (BG.kept_list 48 ParzTS.regs0 ParzTS.regs_out0).
Lemma KS_arzTS_ok : BG.kept_ok 48 ParzTS.regs0 ParzTS.regs_out0 KS_arzTS = true. Proof. vm_compute. reflexivity. Qed.
Lemma arzTS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 11) = Z_to_bv 64 (V 37%nat) -> getr R (reg 13) = Z_to_bv 64 0 ->
  6905856 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 -> aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 -> 0 <= (V 37%nat) <= 22 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((bv_unsigned (getr R (reg 10))) + 0) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((bv_unsigned (getr R (reg 10))) + 0) <= i < ((bv_unsigned (getr R (reg 10))) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xd62a0 M) (st fx' R' 0xd62b8 M')
        /\ (forall x, In x KS_arzTS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 (((bv_unsigned (getr R (reg 10))) + (V 37%nat)) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 ((bv_unsigned (getr R (reg 10))) + 1)
        /\ getr R' (reg 13) = Z_to_bv 64 (2 * (V 37%nat))
        /\ L5.u8_at RSEGS M' (((bv_unsigned (getr R (reg 10))) + (V 37%nat)) + 1) 0
        /\ L5.u8_at RSEGS M' (bv_unsigned (getr R (reg 10))) (2 * (V 37%nat))).
Proof.
  intros pvzI1 pvzI2 G2 G11 G13 pvzI3 K1 K2 pvzI4.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV37l; move HV37l before pvzI2; pose proof (proj2 pvzI2) as HV37r; move HV37r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as K0l; move K0l before pvzI3; pose proof (proj2 pvzI3) as K0r; move K0r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K3l; move K3l before pvzI4; pose proof (proj2 pvzI4) as K3r; move K3r before pvzI4; clear pvzI4.
  set (vz_2 := V 2%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E ParzTS.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParzTS.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParzTS.kn0).
  { unfold know_ok, ParzTS.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K0l K0r) | evalEk ZA ltac:(clear) | clear - K0l K0r; lia | clear - K0l K0r; lia | clear - K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (ParzTS.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParzTS.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((bv_unsigned (getr R (reg 10))) + 0) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 0) + 24) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold ParzTS.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc ParzTS.ps0) with 0xd62b8 in Hms. change (SR.ps_regs ParzTS.ps0) with (map (fun i => (i, nth i ParzTS.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells ParzTS.ps0) with ParzTS.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' ParzTS.regs0 ParzTS.regs_out0 48 KS_arzTS KS_arzTS_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg ParzTS.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParzTS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParzTS.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth ParzTS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParzTS.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth ParzTS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear - K0l K0r HV37l HV37r K3l K3r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - K0l K0r) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K3l K3r) | byte_tac ltac:(clear - HV37l HV37r K3l K3r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module ParzTL := LibSegBa_arzTL_b.
Definition KS_arzTL : list nat := Eval vm_compute in (BG.kept_list 48 ParzTL.regs0 ParzTL.regs_out0).
Lemma KS_arzTL_ok : BG.kept_ok 48 ParzTL.regs0 ParzTL.regs_out0 KS_arzTL = true. Proof. vm_compute. reflexivity. Qed.
Lemma arzTL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 11) = Z_to_bv 64 (V 37%nat) -> getr R (reg 13) = Z_to_bv 64 1 ->
  6905856 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 -> aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 -> 0 <= (V 37%nat) <= 134217728 ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 16) (V 35%nat) -> 4096 <= (V 35%nat) <= 140737488355328 -> L5.writable RSEGS M ((V 35%nat) + (V 37%nat)) 1 -> (((V 35%nat) + (V 37%nat)) + 1 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= ((V 35%nat) + (V 37%nat))) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((bv_unsigned (getr R (reg 10))) + 8) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 8) + 8) -> ~ ((((V 35%nat) + (V 37%nat)) + 0) <= bv_unsigned a < (((V 35%nat) + (V 37%nat)) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((bv_unsigned (getr R (reg 10))) + 8) <= i < ((bv_unsigned (getr R (reg 10))) + 8) + 8) -> ~ ((((V 35%nat) + (V 37%nat)) + 0) <= i < (((V 35%nat) + (V 37%nat)) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xd62a0 M) (st fx' R' 0xd62dc M')
        /\ (forall x, In x KS_arzTL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 35%nat) + (V 37%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 (V 35%nat)
        /\ L5.u8_at RSEGS M' ((V 35%nat) + (V 37%nat)) 0
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 8) (V 37%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G11 G13 pvzI4 K1 K2 pvzI5 K4 pvzI6 K6 K7.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV35l; move HV35l before pvzI2; pose proof (proj2 pvzI2) as HV35r; move HV35r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K3l; move K3l before pvzI5; pose proof (proj2 pvzI5) as K3r; move K3r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K5l; move K5l before pvzI6; pose proof (proj2 pvzI6) as K5r; move K5r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 35%nat => vz_35 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E ParzTL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParzTL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParzTL.kn0).
  { unfold know_ok, ParzTL.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K0l K0r K7) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K0l K0r K7) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K0l K0r K7) | evalEk ZA ltac:(clear) | clear - K0l K0r K7; lia | clear - K0l K0r K7; lia | clear - K0l K0r K7; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K3l K3r K7) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K0l K0r K7) | evalEk ZA ltac:(clear - HV35l HV35r K5l K5r K7) | clear - K0l K0r K7; lia | clear - K0l K0r K7; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K5l K5r K7) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV35l HV35r K5l K5r K7 HV37l HV37r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K5l K5r K7 HV37l HV37r K3l K3r; lia | clear - HV35l HV35r K5l K5r K7 HV37l HV37r K3l K3r; lia | clear - HV35l HV35r K5l K5r K7 HV37l HV37r K3l K3r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K5l K5r K7 HV37l HV37r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K0l K0r K7) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (ParzTL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParzTL.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((bv_unsigned (getr R (reg 10))) + 8) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 8) + 8) -> ~ (((vz_35 + vz_37) + 0) <= bv_unsigned a < ((vz_35 + vz_37) + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold ParzTL.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear - K0l K0r K7 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV35l HV35r K5l K5r K7 HV37l HV37r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV35l HV35r K5l K5r K7 HV37l HV37r K3l K3r Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc ParzTL.ps0) with 0xd62dc in Hms. change (SR.ps_regs ParzTL.ps0) with (map (fun i => (i, nth i ParzTL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells ParzTL.ps0) with ParzTL.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' ParzTL.regs0 ParzTL.regs_out0 48 KS_arzTL KS_arzTL_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg ParzTL.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParzTL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParzTL.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth ParzTL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear - HV35l HV35r K5l K5r K7 HV37l HV37r K3l K3r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K3l K3r K7) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PaapS0 := LibSegBa_aapS0_b.
Definition KS_aapS0_0 : list nat := Eval vm_compute in (BG.kept_list 60 PaapS0.regs0 PaapS0.regs_out0).
Lemma KS_aapS0_0_ok : BG.kept_ok 60 PaapS0.regs0 PaapS0.regs_out0 KS_aapS0_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_aapS0_1 : list nat := Eval vm_compute in (BG.kept_list 60 PaapS0.regs0 PaapS0.regs_out1).
Lemma KS_aapS0_1_ok : BG.kept_ok 60 PaapS0.regs0 PaapS0.regs_out1 KS_aapS0_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma aapS0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 11) = Z_to_bv 64 (V 43%nat) ->
  140735332487248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 6905856 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 -> (((V 2%nat) - 80) + 80 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= ((V 2%nat) - 80)) -> L5.u8_at RSEGS M (bv_unsigned (getr R (reg 10))) (V 33%nat) ->
  0 <= (V 33%nat) <= 44 -> Z.testbit (V 33%nat) 0 = false -> L5.u64_at RSEGS M (bv_unsigned (getr R (reg 10))) (V 36%nat) -> Z.testbit (V 36%nat) 0 = false ->
  0 <= (((72057594037927936 * (V 36%nat)) mod 2 ^ 64) / 144115188075855872) <= 22 -> 1 <= (V 43%nat) <= 67125248 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 80) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 80) <= i < ((V 2%nat) - 80) + 80) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd5d10 M) (st fx' R' 0xd5d74 M')
        /\ (forall x, In x KS_aapS0_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ bv_unsigned (getr R' (reg 11)) = ((((18446744073709551615 * (((72057594037927936 * (V 36%nat)) mod 2 ^ 64) / 144115188075855872)) mod 2 ^ 64) + 22) mod 2 ^ 64)
        /\ bv_unsigned (getr R' (reg 18)) = (((72057594037927936 * (V 36%nat)) mod 2 ^ 64) / 144115188075855872)
        /\ getr R' (reg 23) = Z_to_bv 64 22
        /\ (V 43%nat) <= ((((18446744073709551615 * (((72057594037927936 * (V 36%nat)) mod 2 ^ 64) / 144115188075855872)) mod 2 ^ 64) + 22) mod 2 ^ 64)
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
      \/ (msteps RSEGS (st fx R 0xd5d10 M) (st fx' R' 0xd5d9c M')
        /\ (forall x, In x KS_aapS0_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ bv_unsigned (getr R' (reg 11)) = ((((18446744073709551615 * (((72057594037927936 * (V 36%nat)) mod 2 ^ 64) / 144115188075855872)) mod 2 ^ 64) + 22) mod 2 ^ 64)
        /\ bv_unsigned (getr R' (reg 18)) = (((72057594037927936 * (V 36%nat)) mod 2 ^ 64) / 144115188075855872)
        /\ getr R' (reg 23) = Z_to_bv 64 22
        /\ ((((18446744073709551615 * (((72057594037927936 * (V 36%nat)) mod 2 ^ 64) / 144115188075855872)) mod 2 ^ 64) + 22) mod 2 ^ 64) < (V 43%nat)
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
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G11 pvzI5 K1 K2 pvzI6 K4 K5 K6 K7 pvzI7 K9 K10 K11 K12 pvzI8.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV43l; move HV43l before pvzI4; pose proof (proj2 pvzI4) as HV43r; move HV43r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K8l; move K8l before pvzI7; pose proof (proj2 pvzI7) as K8r; move K8r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K13l; move K13l before pvzI8; pose proof (proj2 pvzI8) as K13r; move K13r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_43 := V 43%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 36%nat => Z_to_bv 64 vz_36 | 43%nat => Z_to_bv 64 vz_43 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 36%nat => vz_36 | 43%nat => vz_43 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E PaapS0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaapS0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaapS0.kn0).
  { unfold know_ok, PaapS0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K3l K3r K6) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K3l K3r K6) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K3l K3r K6) | evalEk ZA ltac:(clear) | clear - K3l K3r K6; lia | clear - K3l K3r K6; lia | clear - K3l K3r K6; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - K3l K3r K6) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K9) | clear - K3l K3r K6; lia | clear - K3l K3r K6; lia | byte_tac ltac:(clear - HV33l HV33r K8l K8r K9) | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K9) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K9) | clear; lia | rewrite (L5K.land1_bit0_false vz_33 ltac:(clear - HV33l HV33r K8l K8r K9; lia) K9); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6) | evalEk ZA ltac:(clear - HV36l HV36r K11) | clear - K3l K3r K6; lia | clear - K3l K3r K6; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV36l HV36r K11) | clear; lia | rewrite (L5K.land1_bit0_false vz_36 ltac:(clear - HV36l HV36r K11; lia) K11); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K13l K13r) | exact (conj K13l K13r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaapS0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaapS0.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 80) <= bv_unsigned a < (vz_2 - 80) + 80) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PaapS0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PaapS0.ps0) with 0xd5d74 in Hms. change (SR.ps_regs PaapS0.ps0) with (map (fun i => (i, nth i PaapS0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PaapS0.ps0) with PaapS0.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PaapS0.regs0 PaapS0.regs_out0 60 KS_aapS0_0 KS_aapS0_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PaapS0.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaapS0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PaapS0.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaapS0.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PaapS0.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PaapS0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PaapS0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaapS0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PaapS0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaapS0.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PaapS0.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaapS0.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PaapS0.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PaapS0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
  - right.
    change (SR.ps_pc PaapS0.ps1) with 0xd5d9c in Hms. change (SR.ps_regs PaapS0.ps1) with (map (fun i => (i, nth i PaapS0.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PaapS0.ps1) with PaapS0.cells1 in Hcells. unfold PaapS0.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PaapS0.regs0 PaapS0.regs_out1 60 KS_aapS0_1 KS_aapS0_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PaapS0.regs_out1 E' R' 2 Hregs) by (clear; lia). cbn [nth PaapS0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PaapS0.regs_out1 E' R' 8 Hregs) by (clear; lia). cbn [nth PaapS0.regs_out1]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PaapS0.regs_out1 E' R' 9 Hregs) by (clear; lia). cbn [nth PaapS0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PaapS0.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PaapS0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PaapS0.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PaapS0.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PaapS0.regs_out1 E' R' 18 Hregs) by (clear; lia). cbn [nth PaapS0.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PaapS0.regs_out1 E' R' 23 Hregs) by (clear; lia). cbn [nth PaapS0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PaapL0 := LibSegBa_aapL0_b.
Definition KS_aapL0_0 : list nat := Eval vm_compute in (BG.kept_list 60 PaapL0.regs0 PaapL0.regs_out0).
Lemma KS_aapL0_0_ok : BG.kept_ok 60 PaapL0.regs0 PaapL0.regs_out0 KS_aapL0_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_aapL0_1 : list nat := Eval vm_compute in (BG.kept_list 60 PaapL0.regs0 PaapL0.regs_out1).
Lemma KS_aapL0_1_ok : BG.kept_ok 60 PaapL0.regs0 PaapL0.regs_out1 KS_aapL0_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma aapL0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 11) = Z_to_bv 64 (V 43%nat) ->
  140735332487248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 6905856 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 -> (((V 2%nat) - 80) + 80 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= ((V 2%nat) - 80)) -> L5.u8_at RSEGS M (bv_unsigned (getr R (reg 10))) (V 33%nat) ->
  0 <= (V 33%nat) <= 255 -> Z.testbit (V 33%nat) 0 = true -> L5.u64_at RSEGS M (bv_unsigned (getr R (reg 10))) (V 36%nat) -> Z.testbit (V 36%nat) 0 = true ->
  27 <= (V 36%nat) <= 134217729 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 34%nat) -> 0 <= (V 34%nat) <= 134217728 -> 1 <= (V 43%nat) <= 67125248 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 80) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 80) <= i < ((V 2%nat) - 80) + 80) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd5d10 M) (st fx' R' 0xd5d74 M')
        /\ (forall x, In x KS_aapL0_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 ((((-1) * (V 34%nat)) + (2 * ((V 36%nat) / 2))) - 1)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 ((2 * ((V 36%nat) / 2)) - 1)
        /\ (V 43%nat) <= ((((((18446744073709551615 * (V 34%nat)) mod 2 ^ 64) + ((2 * ((V 36%nat) / 2)) mod 2 ^ 64)) mod 2 ^ 64) + 18446744073709551615) mod 2 ^ 64)
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
      \/ (msteps RSEGS (st fx R 0xd5d10 M) (st fx' R' 0xd5d9c M')
        /\ (forall x, In x KS_aapL0_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 ((((-1) * (V 34%nat)) + (2 * ((V 36%nat) / 2))) - 1)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 ((2 * ((V 36%nat) / 2)) - 1)
        /\ ((((((18446744073709551615 * (V 34%nat)) mod 2 ^ 64) + ((2 * ((V 36%nat) / 2)) mod 2 ^ 64)) mod 2 ^ 64) + 18446744073709551615) mod 2 ^ 64) < (V 43%nat)
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
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G11 pvzI6 K1 K2 pvzI7 K4 K5 K6 K7 pvzI8 K9 K10 K11 pvzI9 K13 pvzI10 pvzI11.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV43l; move HV43l before pvzI5; pose proof (proj2 pvzI5) as HV43r; move HV43r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K8l; move K8l before pvzI8; pose proof (proj2 pvzI8) as K8r; move K8r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K12l; move K12l before pvzI9; pose proof (proj2 pvzI9) as K12r; move K12r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K14l; move K14l before pvzI10; pose proof (proj2 pvzI10) as K14r; move K14r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K15l; move K15l before pvzI11; pose proof (proj2 pvzI11) as K15r; move K15r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_43 := V 43%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 43%nat => Z_to_bv 64 vz_43 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 43%nat => vz_43 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E PaapL0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaapL0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaapL0.kn0).
  { unfold know_ok, PaapL0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K3l K3r K6) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K3l K3r K6) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K3l K3r K6) | evalEk ZA ltac:(clear) | clear - K3l K3r K6; lia | clear - K3l K3r K6; lia | clear - K3l K3r K6; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - K3l K3r K6) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K9) | clear - K3l K3r K6; lia | clear - K3l K3r K6; lia | byte_tac ltac:(clear - HV33l HV33r K8l K8r K9) | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K9) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K9) | clear; lia | rewrite (L5K.land1_bit0_true vz_33 ltac:(clear - HV33l HV33r K8l K8r K9; lia) K9); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6) | evalEk ZA ltac:(clear - HV36l HV36r K11 K12l K12r) | clear - K3l K3r K6; lia | clear - K3l K3r K6; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV36l HV36r K11 K12l K12r) | clear; lia | rewrite (L5K.land1_bit0_true vz_36 ltac:(clear - HV36l HV36r K11 K12l K12r; lia) K11); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K11 K12l K12r) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r) | clear - K3l K3r K6; lia | clear - K3l K3r K6; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K15l K15r) | exact (conj K15l K15r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaapL0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaapL0.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 80) <= bv_unsigned a < (vz_2 - 80) + 80) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PaapL0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PaapL0.ps0) with 0xd5d74 in Hms. change (SR.ps_regs PaapL0.ps0) with (map (fun i => (i, nth i PaapL0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PaapL0.ps0) with PaapL0.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PaapL0.regs0 PaapL0.regs_out0 60 KS_aapL0_0 KS_aapL0_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PaapL0.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaapL0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PaapL0.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaapL0.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PaapL0.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PaapL0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PaapL0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaapL0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PaapL0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaapL0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PaapL0.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaapL0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PaapL0.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PaapL0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
  - right.
    change (SR.ps_pc PaapL0.ps1) with 0xd5d9c in Hms. change (SR.ps_regs PaapL0.ps1) with (map (fun i => (i, nth i PaapL0.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PaapL0.ps1) with PaapL0.cells1 in Hcells. unfold PaapL0.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PaapL0.regs0 PaapL0.regs_out1 60 KS_aapL0_1 KS_aapL0_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PaapL0.regs_out1 E' R' 2 Hregs) by (clear; lia). cbn [nth PaapL0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PaapL0.regs_out1 E' R' 8 Hregs) by (clear; lia). cbn [nth PaapL0.regs_out1]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PaapL0.regs_out1 E' R' 9 Hregs) by (clear; lia). cbn [nth PaapL0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PaapL0.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PaapL0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PaapL0.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PaapL0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PaapL0.regs_out1 E' R' 18 Hregs) by (clear; lia). cbn [nth PaapL0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PaapL0.regs_out1 E' R' 23 Hregs) by (clear; lia). cbn [nth PaapL0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PafitS := LibSegBa_afitS_b.
Definition KS_afitS : list nat := Eval vm_compute in (BG.kept_list 60 PafitS.regs0 PafitS.regs_out0).
Lemma KS_afitS_ok : BG.kept_ok 60 PafitS.regs0 PafitS.regs_out0 KS_afitS = true. Proof. vm_compute. reflexivity. Qed.
Lemma afitS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 43%nat) -> getr R (reg 10) = Z_to_bv 64 0 -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 22 ->
  140735332487248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 6905856 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 24 -> (((V 2%nat) - 80) + 80 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 80)) -> 0 <= (V 34%nat) <= 22 ->
  1 <= (V 43%nat) <= 22 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xd5d74 M) (st fx' R' 0x77c88 M')
        /\ (forall x, In x KS_afitS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 876172
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 10%nat) + (V 34%nat)) + 1)
        /\ getr R' (reg 11) = getr R (reg 12)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 10%nat) + 1)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 34%nat) + (V 43%nat))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G10 G18 G23 pvzI5 K1 K2 pvzI6 K4 K5 K6 pvzI7 pvzI8.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV43l; move HV43l before pvzI4; pose proof (proj2 pvzI4) as HV43r; move HV43r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K7l; move K7l before pvzI7; pose proof (proj2 pvzI7) as K7r; move K7r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K8l; move K8l before pvzI8; pose proof (proj2 pvzI8) as K8r; move K8r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_43 := V 43%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 34%nat => Z_to_bv 64 vz_34 | 43%nat => Z_to_bv 64 vz_43 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 34%nat => vz_34 | 43%nat => vz_43 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E PafitS.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PafitS.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PafitS.kn0).
  { unfold know_ok, PafitS.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PafitS.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PafitS.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PafitS.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PafitS.ps0) with 0x77c88 in Hms. change (SR.ps_regs PafitS.ps0) with (map (fun i => (i, nth i PafitS.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PafitS.ps0) with PafitS.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PafitS.regs0 PafitS.regs_out0 60 KS_afitS KS_afitS_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PafitS.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PafitS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafitS.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PafitS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafitS.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PafitS.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PafitS.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PafitS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafitS.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PafitS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PafitS.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PafitS.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PafitL := LibSegBa_afitL_b.
Definition KS_afitL : list nat := Eval vm_compute in (BG.kept_list 60 PafitL.regs0 PafitL.regs_out0).
Lemma KS_afitL_ok : BG.kept_ok 60 PafitL.regs0 PafitL.regs_out0 KS_afitL = true. Proof. vm_compute. reflexivity. Qed.
Lemma afitL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 43%nat) -> getr R (reg 10) = Z_to_bv 64 1 -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332487248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 6905856 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 24 -> (((V 2%nat) - 80) + 80 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 80)) -> 0 <= (V 34%nat) <= 134217728 ->
  1 <= (V 43%nat) <= 67125248 -> L5.u64_at RSEGS M ((V 10%nat) + 16) (V 35%nat) -> 4096 <= (V 35%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xd5d74 M) (st fx' R' 0x77c88 M')
        /\ (forall x, In x KS_afitL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 876172
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 34%nat) + (V 35%nat))
        /\ getr R' (reg 11) = getr R (reg 12)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 34%nat) + (V 43%nat))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G18 pvzI6 K1 K2 pvzI7 K4 K5 K6 pvzI8 pvzI9 K9 pvzI10.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV43l; move HV43l before pvzI5; pose proof (proj2 pvzI5) as HV43r; move HV43r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K7l; move K7l before pvzI8; pose proof (proj2 pvzI8) as K7r; move K7r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K8l; move K8l before pvzI9; pose proof (proj2 pvzI9) as K8r; move K8r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K10l; move K10l before pvzI10; pose proof (proj2 pvzI10) as K10r; move K10r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_43 := V 43%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 43%nat => Z_to_bv 64 vz_43 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 34%nat => vz_34 | 35%nat => vz_35 | 43%nat => vz_43 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E PafitL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PafitL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PafitL.kn0).
  { unfold know_ok, PafitL.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear - HV35l HV35r K10l K10r) | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PafitL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PafitL.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PafitL.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PafitL.ps0) with 0x77c88 in Hms. change (SR.ps_regs PafitL.ps0) with (map (fun i => (i, nth i PafitL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PafitL.ps0) with PafitL.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PafitL.regs0 PafitL.regs_out0 60 KS_afitL KS_afitL_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PafitL.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PafitL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafitL.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PafitL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafitL.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PafitL.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PafitL.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PafitL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafitL.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PafitL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PafitL.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PafitL.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PaapMS := LibSegBa_aapMS_b.
Definition KS_aapMS : list nat := Eval vm_compute in (BG.kept_list 60 PaapMS.regs0 PaapMS.regs_out0).
Lemma KS_aapMS_ok : BG.kept_ok 60 PaapMS.regs0 PaapMS.regs_out0 KS_aapMS = true. Proof. vm_compute. reflexivity. Qed.
Lemma aapMS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 54%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 10%nat) + 1) -> getr R (reg 22) = Z_to_bv 64 (V 38%nat) ->
  140735332487248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 6905856 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 24 -> (((V 2%nat) - 80) + 80 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 80)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 52%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (V 53%nat) -> L5.u8_at RSEGS M (V 10%nat) (V 33%nat) -> 0 <= (V 33%nat) <= 255 -> Z.testbit (V 33%nat) 0 = false ->
  1 <= (V 38%nat) <= 22 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 10%nat) + 0) <= bv_unsigned a < ((V 10%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 10%nat) + 0) <= i < ((V 10%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xd5e8c M) (st fx' R' 0xd5ee0 M')
        /\ (forall x, In x KS_aapMS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 10%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 53%nat)
        /\ L5.u8_at RSEGS M' (((V 10%nat) + (V 38%nat)) + 1) 0
        /\ L5.u8_at RSEGS M' (V 10%nat) (2 * (V 38%nat))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 G2 G8 G10 G20 G22 pvzI16 K1 K2 pvzI17 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 pvzI18 K19 pvzI19.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV44l; move HV44l before pvzI5; pose proof (proj2 pvzI5) as HV44r; move HV44r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV45l; move HV45l before pvzI6; pose proof (proj2 pvzI6) as HV45r; move HV45r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV46l; move HV46l before pvzI7; pose proof (proj2 pvzI7) as HV46r; move HV46r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV47l; move HV47l before pvzI8; pose proof (proj2 pvzI8) as HV47r; move HV47r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV48l; move HV48l before pvzI9; pose proof (proj2 pvzI9) as HV48r; move HV48r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV49l; move HV49l before pvzI10; pose proof (proj2 pvzI10) as HV49r; move HV49r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV50l; move HV50l before pvzI11; pose proof (proj2 pvzI11) as HV50r; move HV50r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV51l; move HV51l before pvzI12; pose proof (proj2 pvzI12) as HV51r; move HV51r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV52l; move HV52l before pvzI13; pose proof (proj2 pvzI13) as HV52r; move HV52r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV53l; move HV53l before pvzI14; pose proof (proj2 pvzI14) as HV53r; move HV53r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV54l; move HV54l before pvzI15; pose proof (proj2 pvzI15) as HV54r; move HV54r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K0l; move K0l before pvzI16; pose proof (proj2 pvzI16) as K0r; move K0r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K3l; move K3l before pvzI17; pose proof (proj2 pvzI17) as K3r; move K3r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K18l; move K18l before pvzI18; pose proof (proj2 pvzI18) as K18r; move K18r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K20l; move K20l before pvzI19; pose proof (proj2 pvzI19) as K20r; move K20r before pvzI19; clear pvzI19.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *. set (vz_54 := V 54%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 33%nat => Z_to_bv 64 vz_33 | 38%nat => Z_to_bv 64 vz_38 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | 54%nat => Z_to_bv 64 vz_54 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 33%nat => vz_33 | 38%nat => vz_38 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | 53%nat => vz_53 | 54%nat => vz_54 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 55%nat. }
  assert (HR: regs_ok E PaapMS.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaapMS.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaapMS.kn0).
  { unfold know_ok, PaapMS.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear - HV33l HV33r K18l K18r K19) | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | byte_tac ltac:(clear - HV33l HV33r K18l K18r K19) | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K18l K18r K19) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K18l K18r K19) | clear; lia | rewrite (L5K.land1_bit0_false vz_33 ltac:(clear - HV33l HV33r K18l K18r K19; lia) K19); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaapMS.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaapMS.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_10 + 0) <= bv_unsigned a < (vz_10 + 0) + 24) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PaapMS.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk' ZA Hag ltac:(clear) | clear - HV10l HV10r K3l K3r K6 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaapMS.ps0) with 0xd5ee0 in Hms. change (SR.ps_regs PaapMS.ps0) with (map (fun i => (i, nth i PaapMS.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaapMS.ps0) with PaapMS.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaapMS.regs0 PaapMS.regs_out0 60 KS_aapMS KS_aapMS_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaapMS.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaapMS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaapMS.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaapMS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaapMS.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaapMS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaapMS.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PaapMS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaapMS.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaapMS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaapMS.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaapMS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaapMS.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaapMS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaapMS.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PaapMS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaapMS.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PaapMS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaapMS.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PaapMS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaapMS.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PaapMS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaapMS.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PaapMS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6 HV38l HV38r K20l K20r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk' ZA Hag ltac:(clear - HV38l HV38r K20l K20r) | byte_tac ltac:(clear - HV38l HV38r K20l K20r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PaapML := LibSegBa_aapML_b.
Definition KS_aapML : list nat := Eval vm_compute in (BG.kept_list 60 PaapML.regs0 PaapML.regs_out0).
Lemma KS_aapML_ok : BG.kept_ok 60 PaapML.regs0 PaapML.regs_out0 KS_aapML = true. Proof. vm_compute. reflexivity. Qed.
Lemma aapML_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 54%nat) -> getr R (reg 20) = Z_to_bv 64 (V 35%nat) -> getr R (reg 22) = Z_to_bv 64 (V 38%nat) ->
  140735332487248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 6905856 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 24 -> (((V 2%nat) - 80) + 80 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 80)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 52%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (V 53%nat) -> L5.u8_at RSEGS M (V 10%nat) (V 33%nat) -> 0 <= (V 33%nat) <= 255 -> Z.testbit (V 33%nat) 0 = true ->
  1 <= (V 38%nat) <= 67125248 -> 4096 <= (V 35%nat) <= 140737488355328 -> L5.writable RSEGS M ((V 35%nat) + (V 38%nat)) 1 -> (((V 35%nat) + (V 38%nat)) + 1 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 35%nat) + (V 38%nat))) ->
  (((V 35%nat) + (V 38%nat)) + 1 <= ((V 2%nat) - 80) \/ ((V 2%nat) - 80) + 80 <= ((V 35%nat) + (V 38%nat))) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 10%nat) + 8) <= bv_unsigned a < ((V 10%nat) + 8) + 8) -> ~ ((((V 35%nat) + (V 38%nat)) + 0) <= bv_unsigned a < (((V 35%nat) + (V 38%nat)) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 10%nat) + 8) <= i < ((V 10%nat) + 8) + 8) -> ~ ((((V 35%nat) + (V 38%nat)) + 0) <= i < (((V 35%nat) + (V 38%nat)) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xd5e8c M) (st fx' R' 0xd5ee0 M')
        /\ (forall x, In x KS_aapML -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 10%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 53%nat)
        /\ L5.u8_at RSEGS M' ((V 35%nat) + (V 38%nat)) 0
        /\ L5.u64_at RSEGS M' ((V 10%nat) + 8) (V 38%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 G2 G8 G10 G20 G22 pvzI17 K1 K2 pvzI18 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 pvzI19 K19 pvzI20 pvzI21 K22 K23 K24.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV44l; move HV44l before pvzI6; pose proof (proj2 pvzI6) as HV44r; move HV44r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV45l; move HV45l before pvzI7; pose proof (proj2 pvzI7) as HV45r; move HV45r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV46l; move HV46l before pvzI8; pose proof (proj2 pvzI8) as HV46r; move HV46r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV47l; move HV47l before pvzI9; pose proof (proj2 pvzI9) as HV47r; move HV47r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV48l; move HV48l before pvzI10; pose proof (proj2 pvzI10) as HV48r; move HV48r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV49l; move HV49l before pvzI11; pose proof (proj2 pvzI11) as HV49r; move HV49r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV50l; move HV50l before pvzI12; pose proof (proj2 pvzI12) as HV50r; move HV50r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV51l; move HV51l before pvzI13; pose proof (proj2 pvzI13) as HV51r; move HV51r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV52l; move HV52l before pvzI14; pose proof (proj2 pvzI14) as HV52r; move HV52r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV53l; move HV53l before pvzI15; pose proof (proj2 pvzI15) as HV53r; move HV53r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV54l; move HV54l before pvzI16; pose proof (proj2 pvzI16) as HV54r; move HV54r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K0l; move K0l before pvzI17; pose proof (proj2 pvzI17) as K0r; move K0r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K3l; move K3l before pvzI18; pose proof (proj2 pvzI18) as K3r; move K3r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K18l; move K18l before pvzI19; pose proof (proj2 pvzI19) as K18r; move K18r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K20l; move K20l before pvzI20; pose proof (proj2 pvzI20) as K20r; move K20r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K21l; move K21l before pvzI21; pose proof (proj2 pvzI21) as K21r; move K21r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *. set (vz_54 := V 54%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 38%nat => Z_to_bv 64 vz_38 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | 54%nat => Z_to_bv 64 vz_54 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 33%nat => vz_33 | 35%nat => vz_35 | 38%nat => vz_38 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | 53%nat => vz_53 | 54%nat => vz_54 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 55%nat. }
  assert (HR: regs_ok E PaapML.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaapML.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaapML.kn0).
  { unfold know_ok, PaapML.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K24; lia | clear - HV2l HV2r K0l K0r K6 K24; lia | clear - HV2l HV2r K0l K0r K6 K24; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K23) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K23) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K23) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K3l K3r K6 K23; lia | clear - HV10l HV10r K3l K3r K6 K23; lia | clear - HV10l HV10r K3l K3r K6 K23; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K23) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K6 K24; lia | clear - HV2l HV2r K0l K0r K6 K24; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K6 K24; lia | clear - HV2l HV2r K0l K0r K6 K24; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K6 K24; lia | clear - HV2l HV2r K0l K0r K6 K24; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K6 K24; lia | clear - HV2l HV2r K0l K0r K6 K24; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K6 K24; lia | clear - HV2l HV2r K0l K0r K6 K24; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K6 K24; lia | clear - HV2l HV2r K0l K0r K6 K24; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K6 K24; lia | clear - HV2l HV2r K0l K0r K6 K24; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r K6 K24; lia | clear - HV2l HV2r K0l K0r K6 K24; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K0l K0r K6 K24; lia | clear - HV2l HV2r K0l K0r K6 K24; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K0l K0r K6 K24; lia | clear - HV2l HV2r K0l K0r K6 K24; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV33l HV33r K18l K18r K19) | clear - HV10l HV10r K3l K3r K6 K23; lia | clear - HV10l HV10r K3l K3r K6 K23; lia | byte_tac ltac:(clear - HV33l HV33r K18l K18r K19) | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K18l K18r K19) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K18l K18r K19) | clear; lia | rewrite (L5K.land1_bit0_true vz_33 ltac:(clear - HV33l HV33r K18l K18r K19; lia) K19); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K20l K20r K23 K24) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K21l K21r K23 K24) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV35l HV35r K21l K21r K23 K24 HV38l HV38r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K21l K21r K23 K24 HV38l HV38r K20l K20r; lia | clear - HV35l HV35r K21l K21r K23 K24 HV38l HV38r K20l K20r; lia | clear - HV35l HV35r K21l K21r K23 K24 HV38l HV38r K20l K20r; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K21l K21r K23 K24 HV38l HV38r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K23) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K21l K21r K23 K24 HV38l HV38r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaapML.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaapML.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_10 + 8) <= bv_unsigned a < (vz_10 + 8) + 8) -> ~ (((vz_35 + vz_38) + 0) <= bv_unsigned a < ((vz_35 + vz_38) + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PaapML.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6 K23) | evalEk' ZA Hag ltac:(clear) | clear - HV10l HV10r K3l K3r K6 K23 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV35l HV35r K21l K21r K23 K24 HV38l HV38r K20l K20r) | evalEk' ZA Hag ltac:(clear) | clear - HV35l HV35r K21l K21r K23 K24 HV38l HV38r K20l K20r Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaapML.ps0) with 0xd5ee0 in Hms. change (SR.ps_regs PaapML.ps0) with (map (fun i => (i, nth i PaapML.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaapML.ps0) with PaapML.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaapML.regs0 PaapML.regs_out0 60 KS_aapML KS_aapML_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaapML.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaapML.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaapML.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaapML.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaapML.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaapML.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaapML.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PaapML.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaapML.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaapML.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaapML.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaapML.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaapML.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaapML.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaapML.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PaapML.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaapML.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PaapML.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaapML.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PaapML.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaapML.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PaapML.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaapML.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PaapML.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear - HV35l HV35r K21l K21r K23 K24 HV38l HV38r K20l K20r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6 K23) | evalEk' ZA Hag ltac:(clear - HV38l HV38r K20l K20r K23 K24) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PagrowS := LibSegBa_agrowS_b.
Definition KS_agrowS_0 : list nat := Eval vm_compute in (BG.kept_list 60 PagrowS.regs0 PagrowS.regs_out0).
Lemma KS_agrowS_0_ok : BG.kept_ok 60 PagrowS.regs0 PagrowS.regs_out0 KS_agrowS_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_agrowS_1 : list nat := Eval vm_compute in (BG.kept_list 60 PagrowS.regs0 PagrowS.regs_out1).
Lemma KS_agrowS_1_ok : BG.kept_ok 60 PagrowS.regs0 PagrowS.regs_out1 KS_agrowS_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma agrowS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 43%nat) -> getr R (reg 10) = Z_to_bv 64 0 -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 22 ->
  140735332487248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 6905856 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 24 -> (((V 2%nat) - 80) + 80 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 80)) -> 0 <= (V 34%nat) <= 22 ->
  1 <= (V 43%nat) <= 67125248 -> 1 <= (((V 34%nat) + (V 43%nat)) - 22) <= 67125248 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd5d9c M) (st fx' R' 0xd5e14 M')
        /\ (forall x, In x KS_agrowS_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 34%nat) + (V 43%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 23
        /\ getr R' (reg 13) = Z_to_bv 64 (((V 34%nat) + (V 43%nat)) - 22)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 10%nat) + 1)
        /\ getr R' (reg 21) = Z_to_bv 64 ((8 * (((V 34%nat) + (V 43%nat)) / 8)) + 7)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 34%nat) + (V 43%nat))
        /\ 44 < (((V 34%nat) + (V 43%nat)) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xd5d9c M) (st fx' R' 0x130338 M')
        /\ (forall x, In x KS_agrowS_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 876092
        /\ getr R' (reg 10) = Z_to_bv 64 48
        /\ getr R' (reg 11) = Z_to_bv 64 23
        /\ getr R' (reg 13) = Z_to_bv 64 (((V 34%nat) + (V 43%nat)) - 22)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 10%nat) + 1)
        /\ getr R' (reg 21) = Z_to_bv 64 48
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 34%nat) + (V 43%nat))
        /\ getr R' (reg 24) = getr R (reg 12)
        /\ (((V 34%nat) + (V 43%nat)) mod 2 ^ 64) <= 44)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G10 G18 G23 pvzI5 K1 K2 pvzI6 K4 K5 K6 pvzI7 pvzI8 pvzI9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV43l; move HV43l before pvzI4; pose proof (proj2 pvzI4) as HV43r; move HV43r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K7l; move K7l before pvzI7; pose proof (proj2 pvzI7) as K7r; move K7r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K8l; move K8l before pvzI8; pose proof (proj2 pvzI8) as K8r; move K8r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K9l; move K9l before pvzI9; pose proof (proj2 pvzI9) as K9r; move K9r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_43 := V 43%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 34%nat => Z_to_bv 64 vz_34 | 43%nat => Z_to_bv 64 vz_43 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 34%nat => vz_34 | 43%nat => vz_43 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E PagrowS.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PagrowS.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PagrowS.kn0).
  { unfold know_ok, PagrowS.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K7l K7r K9l K9r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K8l K8r K9l K9r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K7l K7r K9l K9r HV43l HV43r K8l K8r) | exact (conj K9l K9r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PagrowS.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PagrowS.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PagrowS.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PagrowS.ps0) with 0xd5e14 in Hms. change (SR.ps_regs PagrowS.ps0) with (map (fun i => (i, nth i PagrowS.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PagrowS.ps0) with PagrowS.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PagrowS.regs0 PagrowS.regs_out0 60 KS_agrowS_0 KS_agrowS_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PagrowS.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PagrowS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PagrowS.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PagrowS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PagrowS.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PagrowS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PagrowS.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PagrowS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PagrowS.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PagrowS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PagrowS.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PagrowS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  - right.
    change (SR.ps_pc PagrowS.ps1) with 0x130338 in Hms. change (SR.ps_regs PagrowS.ps1) with (map (fun i => (i, nth i PagrowS.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PagrowS.ps1) with PagrowS.cells1 in Hcells. unfold PagrowS.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PagrowS.regs0 PagrowS.regs_out1 60 KS_agrowS_1 KS_agrowS_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PagrowS.regs_out1 E' R' 1 Hregs) by (clear; lia). cbn [nth PagrowS.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PagrowS.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PagrowS.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PagrowS.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PagrowS.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PagrowS.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PagrowS.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PagrowS.regs_out1 E' R' 19 Hregs) by (clear; lia). cbn [nth PagrowS.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PagrowS.regs_out1 E' R' 21 Hregs) by (clear; lia). cbn [nth PagrowS.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PagrowS.regs_out1 E' R' 22 Hregs) by (clear; lia). cbn [nth PagrowS.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PagrowS.regs_out1 E' R' 24 Hregs) by (clear; lia). cbn [nth PagrowS.regs_out1]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PagrowL := LibSegBa_agrowL_b.
Definition KS_agrowL_0 : list nat := Eval vm_compute in (BG.kept_list 60 PagrowL.regs0 PagrowL.regs_out0).
Lemma KS_agrowL_0_ok : BG.kept_ok 60 PagrowL.regs0 PagrowL.regs_out0 KS_agrowL_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_agrowL_1 : list nat := Eval vm_compute in (BG.kept_list 60 PagrowL.regs0 PagrowL.regs_out1).
Lemma KS_agrowL_1_ok : BG.kept_ok 60 PagrowL.regs0 PagrowL.regs_out1 KS_agrowL_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma agrowL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 43%nat) -> getr R (reg 10) = Z_to_bv 64 1 -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 (V 37%nat) ->
  140735332487248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 6905856 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 24 -> (((V 2%nat) - 80) + 80 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 80)) -> 0 <= (V 34%nat) <= 134217728 ->
  1 <= (V 43%nat) <= 67125248 -> 25 <= (V 37%nat) <= 134217728 -> 1 <= ((V 34%nat) + (((-1) * (V 37%nat)) + (V 43%nat))) <= 67125248 -> L5.u64_at RSEGS M ((V 10%nat) + 16) (V 35%nat) ->
  4096 <= (V 35%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd5d9c M) (st fx' R' 0xd5e14 M')
        /\ (forall x, In x KS_agrowL_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 34%nat) + (V 43%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 23
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 34%nat) + (((-1) * (V 37%nat)) + (V 43%nat)))
        /\ getr R' (reg 19) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 ((8 * (((V 34%nat) + (V 43%nat)) / 8)) + 7)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 34%nat) + (V 43%nat))
        /\ ((2 * (V 37%nat)) mod 2 ^ 64) < (((V 34%nat) + (V 43%nat)) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xd5d9c M) (st fx' R' 0x130338 M')
        /\ (forall x, In x KS_agrowL_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 876092
        /\ getr R' (reg 10) = Z_to_bv 64 ((8 * ((2 * (V 37%nat)) / 8)) + 8)
        /\ getr R' (reg 11) = Z_to_bv 64 23
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 34%nat) + (((-1) * (V 37%nat)) + (V 43%nat)))
        /\ getr R' (reg 19) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 ((8 * ((2 * (V 37%nat)) / 8)) + 8)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 34%nat) + (V 43%nat))
        /\ getr R' (reg 24) = getr R (reg 12)
        /\ (((V 34%nat) + (V 43%nat)) mod 2 ^ 64) <= ((2 * (V 37%nat)) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G10 G18 G23 pvzI7 K1 K2 pvzI8 K4 K5 K6 pvzI9 pvzI10 pvzI11 pvzI12 K11 pvzI13.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV43l; move HV43l before pvzI6; pose proof (proj2 pvzI6) as HV43r; move HV43r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K7l; move K7l before pvzI9; pose proof (proj2 pvzI9) as K7r; move K7r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K8l; move K8l before pvzI10; pose proof (proj2 pvzI10) as K8r; move K8r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K9l; move K9l before pvzI11; pose proof (proj2 pvzI11) as K9r; move K9r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K10l; move K10l before pvzI12; pose proof (proj2 pvzI12) as K10r; move K10r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K12l; move K12l before pvzI13; pose proof (proj2 pvzI13) as K12r; move K12r before pvzI13; clear pvzI13.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_43 := V 43%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | 43%nat => Z_to_bv 64 vz_43 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 34%nat => vz_34 | 35%nat => vz_35 | 37%nat => vz_37 | 43%nat => vz_43 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E PagrowL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PagrowL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PagrowL.kn0).
  { unfold know_ok, PagrowL.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K7l K7r K10l K10r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K8l K8r K10l K10r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K9l K9r K10l K10r) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K7l K7r K10l K10r HV37l HV37r K9l K9r HV43l HV43r K8l K8r) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear - HV35l HV35r K12l K12r) | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K12l K12r) | exact (conj K12l K12r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PagrowL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PagrowL.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PagrowL.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PagrowL.ps0) with 0xd5e14 in Hms. change (SR.ps_regs PagrowL.ps0) with (map (fun i => (i, nth i PagrowL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PagrowL.ps0) with PagrowL.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PagrowL.regs0 PagrowL.regs_out0 60 KS_agrowL_0 KS_agrowL_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PagrowL.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PagrowL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PagrowL.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PagrowL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PagrowL.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PagrowL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PagrowL.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PagrowL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PagrowL.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PagrowL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PagrowL.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PagrowL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  - right.
    change (SR.ps_pc PagrowL.ps1) with 0x130338 in Hms. change (SR.ps_regs PagrowL.ps1) with (map (fun i => (i, nth i PagrowL.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PagrowL.ps1) with PagrowL.cells1 in Hcells. unfold PagrowL.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PagrowL.regs0 PagrowL.regs_out1 60 KS_agrowL_1 KS_agrowL_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PagrowL.regs_out1 E' R' 1 Hregs) by (clear; lia). cbn [nth PagrowL.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PagrowL.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PagrowL.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PagrowL.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PagrowL.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PagrowL.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PagrowL.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PagrowL.regs_out1 E' R' 19 Hregs) by (clear; lia). cbn [nth PagrowL.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PagrowL.regs_out1 E' R' 21 Hregs) by (clear; lia). cbn [nth PagrowL.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PagrowL.regs_out1 E' R' 22 Hregs) by (clear; lia). cbn [nth PagrowL.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PagrowL.regs_out1 E' R' 24 Hregs) by (clear; lia). cbn [nth PagrowL.regs_out1]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Parec := LibSegBa_arec_b.
Definition KS_arec : list nat := Eval vm_compute in (BG.kept_list 60 Parec.regs0 Parec.regs_out0).
Lemma KS_arec_ok : BG.kept_ok 60 Parec.regs0 Parec.regs_out0 KS_arec = true. Proof. vm_compute. reflexivity. Qed.
Lemma arec_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 10) = Z_to_bv 64 (V 39%nat) -> getr R (reg 11) = Z_to_bv 64 23 -> getr R (reg 21) = Z_to_bv 64 (V 40%nat) ->
  140735332487248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 45 <= (V 39%nat) <= 268435456 ->
  47 <= (V 40%nat) <= 268435456 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xd5e14 M) (st fx' R' 0x130338 M')
        /\ (forall x, In x KS_arec -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 876092
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 40%nat) + 1)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 40%nat) + 1)
        /\ getr R' (reg 24) = getr R (reg 12)).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G10 G11 G21 pvzI4 K1 K2 pvzI5 pvzI6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV39l; move HV39l before pvzI2; pose proof (proj2 pvzI2) as HV39r; move HV39r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV40l; move HV40l before pvzI3; pose proof (proj2 pvzI3) as HV40r; move HV40r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K3l; move K3l before pvzI5; pose proof (proj2 pvzI5) as K3r; move K3r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K4l; move K4l before pvzI6; pose proof (proj2 pvzI6) as K4r; move K4r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 39%nat => vz_39 | 40%nat => vz_40 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 41%nat. }
  assert (HR: regs_ok E Parec.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Parec.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Parec.kn0).
  { unfold know_ok, Parec.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Parec.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Parec.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Parec.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Parec.ps0) with 0x130338 in Hms. change (SR.ps_regs Parec.ps0) with (map (fun i => (i, nth i Parec.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Parec.ps0) with Parec.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Parec.regs0 Parec.regs_out0 60 KS_arec KS_arec_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Parec.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Parec.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Parec.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Parec.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Parec.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Parec.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Parec.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Parec.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PapN := LibSegBa_apN_b.
Definition KS_apN_0 : list nat := Eval vm_compute in (BG.kept_list 60 PapN.regs0 PapN.regs_out0).
Lemma KS_apN_0_ok : BG.kept_ok 60 PapN.regs0 PapN.regs_out0 KS_apN_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_apN_1 : list nat := Eval vm_compute in (BG.kept_list 60 PapN.regs0 PapN.regs_out1).
Lemma KS_apN_1_ok : BG.kept_ok 60 PapN.regs0 PapN.regs_out1 KS_apN_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma apN_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 10) = Z_to_bv 64 (V 41%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 (V 42%nat) ->
  140735332487248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 0 <= (V 34%nat) <= 134217728 ->
  4096 <= (V 41%nat) <= 140737488355328 -> 4096 <= (V 42%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd5e3c M) (st fx' R' 0x77c8c M')
        /\ (forall x, In x KS_apN_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 876116
        /\ getr R' (reg 11) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 41%nat)
        /\ 1 <= (((V 34%nat) - 0) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xd5e3c M) (st fx' R' 0xd5e54 M')
        /\ (forall x, In x KS_apN_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 20) = Z_to_bv 64 (V 41%nat)
        /\ (((V 34%nat) - 0) mod 2 ^ 64) < 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G10 G18 G19 pvzI5 K1 K2 pvzI6 pvzI7 pvzI8.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV34l; move HV34l before pvzI2; pose proof (proj2 pvzI2) as HV34r; move HV34r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV41l; move HV41l before pvzI3; pose proof (proj2 pvzI3) as HV41r; move HV41r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV42l; move HV42l before pvzI4; pose proof (proj2 pvzI4) as HV42r; move HV42r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K4l; move K4l before pvzI7; pose proof (proj2 pvzI7) as K4r; move K4r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K5l; move K5l before pvzI8; pose proof (proj2 pvzI8) as K5r; move K5r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 34%nat => Z_to_bv 64 vz_34 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 34%nat => vz_34 | 41%nat => vz_41 | 42%nat => vz_42 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 43%nat. }
  assert (HR: regs_ok E PapN.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapN.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapN.kn0).
  { unfold know_ok, PapN.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K5l K5r) | exact (conj K5l K5r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PapN.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapN.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PapN.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PapN.ps0) with 0x77c8c in Hms. change (SR.ps_regs PapN.ps0) with (map (fun i => (i, nth i PapN.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PapN.ps0) with PapN.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PapN.regs0 PapN.regs_out0 60 KS_apN_0 KS_apN_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PapN.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PapN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PapN.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PapN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PapN.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PapN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PapN.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PapN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  - right.
    change (SR.ps_pc PapN.ps1) with 0xd5e54 in Hms. change (SR.ps_regs PapN.ps1) with (map (fun i => (i, nth i PapN.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PapN.ps1) with PapN.cells1 in Hcells. unfold PapN.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PapN.regs0 PapN.regs_out1 60 KS_apN_1 KS_apN_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PapN.regs_out1 E' R' 20 Hregs) by (clear; lia). cbn [nth PapN.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PapDS := LibSegBa_apDS_b.
Definition KS_apDS : list nat := Eval vm_compute in (BG.kept_list 60 PapDS.regs0 PapDS.regs_out0).
Lemma KS_apDS_ok : BG.kept_ok 60 PapDS.regs0 PapDS.regs_out0 KS_apDS = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma apDS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 43%nat) -> getr R (reg 10) = Z_to_bv 64 (V 41%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 20) = Z_to_bv 64 (V 41%nat) -> getr R (reg 21) = Z_to_bv 64 (V 40%nat) -> getr R (reg 22) = Z_to_bv 64 (V 38%nat) -> getr R (reg 23) = Z_to_bv 64 22 -> getr R (reg 24) = Z_to_bv 64 (V 56%nat) ->
  140735332487248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 6905856 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 24 -> (((V 2%nat) - 80) + 80 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 80)) -> 0 <= (V 34%nat) <= 22 ->
  4096 <= (V 41%nat) <= 140737488355328 -> 48 <= (V 40%nat) <= 134217728 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 10%nat) + 0) <= bv_unsigned a < ((V 10%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 10%nat) + 0) <= i < ((V 10%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xd5e54 M) (st fx' R' 0x77c88 M')
        /\ (forall x, In x KS_apDS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 876172
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 34%nat) + (V 41%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 56%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 10%nat) + 16) (V 41%nat)
        /\ L5.u64_at RSEGS M' ((V 10%nat) + 8) (V 34%nat)
        /\ L5.u64_at RSEGS M' (V 10%nat) ((2 * ((V 40%nat) / 2)) + 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G10 G18 G20 G21 G22 G23 G24 pvzI9 K1 K2 pvzI10 K4 K5 K6 pvzI11 pvzI12 pvzI13.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV40l; move HV40l before pvzI5; pose proof (proj2 pvzI5) as HV40r; move HV40r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV41l; move HV41l before pvzI6; pose proof (proj2 pvzI6) as HV41r; move HV41r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV43l; move HV43l before pvzI7; pose proof (proj2 pvzI7) as HV43r; move HV43r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV56l; move HV56l before pvzI8; pose proof (proj2 pvzI8) as HV56r; move HV56r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K0l; move K0l before pvzI9; pose proof (proj2 pvzI9) as K0r; move K0r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K7l; move K7l before pvzI11; pose proof (proj2 pvzI11) as K7r; move K7r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K8l; move K8l before pvzI12; pose proof (proj2 pvzI12) as K8r; move K8r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K9l; move K9l before pvzI13; pose proof (proj2 pvzI13) as K9r; move K9r before pvzI13; clear pvzI13.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_56 := V 56%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 34%nat => Z_to_bv 64 vz_34 | 38%nat => Z_to_bv 64 vz_38 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 43%nat => Z_to_bv 64 vz_43 | 56%nat => Z_to_bv 64 vz_56 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 34%nat => vz_34 | 38%nat => vz_38 | 40%nat => vz_40 | 41%nat => vz_41 | 43%nat => vz_43 | 56%nat => vz_56 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 57%nat. }
  assert (HR: regs_ok E PapDS.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapDS.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapDS.kn0).
  { unfold know_ok, PapDS.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PapDS.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapDS.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_10 + 0) <= bv_unsigned a < (vz_10 + 0) + 24) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PapDS.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk' ZA Hag ltac:(clear) | clear - HV10l HV10r K3l K3r K6 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PapDS.ps0) with 0x77c88 in Hms. change (SR.ps_regs PapDS.ps0) with (map (fun i => (i, nth i PapDS.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PapDS.ps0) with PapDS.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PapDS.regs0 PapDS.regs_out0 60 KS_apDS KS_apDS_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PapDS.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PapDS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapDS.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PapDS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapDS.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PapDS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapDS.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PapDS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk' ZA Hag ltac:(clear - HV41l HV41r K8l K8r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K7l K7r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K9l K9r) | clear; lia]. 
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PapDL := LibSegBa_apDL_b.
Definition KS_apDL : list nat := Eval vm_compute in (BG.kept_list 60 PapDL.regs0 PapDL.regs_out0).
Lemma KS_apDL_ok : BG.kept_ok 60 PapDL.regs0 PapDL.regs_out0 KS_apDL = true. Proof. vm_compute. reflexivity. Qed.
Lemma apDL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 19) = Z_to_bv 64 (V 42%nat) -> getr R (reg 23) = Z_to_bv 64 (V 37%nat) ->
  140735332487248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 25 <= (V 37%nat) <= 134217728 ->
  4096 <= (V 42%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xd5e54 M) (st fx' R' 0xd39ac M')
        /\ (forall x, In x KS_apDL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 876136
        /\ getr R' (reg 10) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 37%nat) + 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G19 G23 pvzI4 K1 K2 pvzI5 pvzI6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV37l; move HV37l before pvzI2; pose proof (proj2 pvzI2) as HV37r; move HV37r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV42l; move HV42l before pvzI3; pose proof (proj2 pvzI3) as HV42r; move HV42r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K3l; move K3l before pvzI5; pose proof (proj2 pvzI5) as K3r; move K3r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K4l; move K4l before pvzI6; pose proof (proj2 pvzI6) as K4r; move K4r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_42 := V 42%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 37%nat => Z_to_bv 64 vz_37 | 42%nat => Z_to_bv 64 vz_42 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 37%nat => vz_37 | 42%nat => vz_42 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 43%nat. }
  assert (HR: regs_ok E PapDL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapDL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapDL.kn0).
  { unfold know_ok, PapDL.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PapDL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapDL.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PapDL.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PapDL.ps0) with 0xd39ac in Hms. change (SR.ps_regs PapDL.ps0) with (map (fun i => (i, nth i PapDL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PapDL.ps0) with PapDL.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PapDL.regs0 PapDL.regs_out0 60 KS_apDL KS_apDL_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PapDL.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PapDL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapDL.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PapDL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PapDL.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PapDL.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PapF := LibSegBa_apF_b.
Definition KS_apF : list nat := Eval vm_compute in (BG.kept_list 60 PapF.regs0 PapF.regs_out0).
Lemma KS_apF_ok : BG.kept_ok 60 PapF.regs0 PapF.regs_out0 KS_apF = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma apF_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 43%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 20) = Z_to_bv 64 (V 41%nat) -> getr R (reg 21) = Z_to_bv 64 (V 40%nat) -> getr R (reg 22) = Z_to_bv 64 (V 38%nat) -> getr R (reg 24) = Z_to_bv 64 (V 56%nat) ->
  140735332487248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 6905856 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 24 -> (((V 2%nat) - 80) + 80 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 80)) -> 0 <= (V 34%nat) <= 134217728 ->
  4096 <= (V 41%nat) <= 140737488355328 -> 48 <= (V 40%nat) <= 134217728 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 10%nat) + 0) <= bv_unsigned a < ((V 10%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 10%nat) + 0) <= i < ((V 10%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xd5e68 M) (st fx' R' 0x77c88 M')
        /\ (forall x, In x KS_apF -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 876172
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 34%nat) + (V 41%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 56%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 10%nat) + 16) (V 41%nat)
        /\ L5.u64_at RSEGS M' ((V 10%nat) + 8) (V 34%nat)
        /\ L5.u64_at RSEGS M' (V 10%nat) ((2 * ((V 40%nat) / 2)) + 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G8 G9 G10 G18 G20 G21 G22 G24 pvzI10 K1 K2 pvzI11 K4 K5 K6 pvzI12 pvzI13 pvzI14.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV40l; move HV40l before pvzI5; pose proof (proj2 pvzI5) as HV40r; move HV40r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV41l; move HV41l before pvzI6; pose proof (proj2 pvzI6) as HV41r; move HV41r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV43l; move HV43l before pvzI7; pose proof (proj2 pvzI7) as HV43r; move HV43r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV55l; move HV55l before pvzI8; pose proof (proj2 pvzI8) as HV55r; move HV55r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV56l; move HV56l before pvzI9; pose proof (proj2 pvzI9) as HV56r; move HV56r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K0l; move K0l before pvzI10; pose proof (proj2 pvzI10) as K0r; move K0r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K3l; move K3l before pvzI11; pose proof (proj2 pvzI11) as K3r; move K3r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K7l; move K7l before pvzI12; pose proof (proj2 pvzI12) as K7r; move K7r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K8l; move K8l before pvzI13; pose proof (proj2 pvzI13) as K8r; move K8r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K9l; move K9l before pvzI14; pose proof (proj2 pvzI14) as K9r; move K9r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 34%nat => Z_to_bv 64 vz_34 | 38%nat => Z_to_bv 64 vz_38 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 43%nat => Z_to_bv 64 vz_43 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 34%nat => vz_34 | 38%nat => vz_38 | 40%nat => vz_40 | 41%nat => vz_41 | 43%nat => vz_43 | 55%nat => vz_55 | 56%nat => vz_56 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 57%nat. }
  assert (HR: regs_ok E PapF.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapF.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapF.kn0).
  { unfold know_ok, PapF.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PapF.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapF.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_10 + 0) <= bv_unsigned a < (vz_10 + 0) + 24) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PapF.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk' ZA Hag ltac:(clear) | clear - HV10l HV10r K3l K3r K6 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PapF.ps0) with 0x77c88 in Hms. change (SR.ps_regs PapF.ps0) with (map (fun i => (i, nth i PapF.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PapF.ps0) with PapF.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PapF.regs0 PapF.regs_out0 60 KS_apF KS_apF_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PapF.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PapF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapF.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PapF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapF.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PapF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapF.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PapF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk' ZA Hag ltac:(clear - HV41l HV41r K8l K8r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K7l K7r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K9l K9r) | clear; lia]. 
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)

End PMARZP.
