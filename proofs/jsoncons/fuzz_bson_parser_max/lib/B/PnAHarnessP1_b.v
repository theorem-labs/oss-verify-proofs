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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require LibSegBa_bhaA0_b LibSegBa_bhaA16_b LibSegBa_bhaB_b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNAHP1.
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
Module PbhaA0 := LibSegBa_bhaA0_b.
Definition KS_bhaA0 : list nat := Eval vm_compute in (BG.kept_list 64 PbhaA0.regs0 PbhaA0.regs_out0).
Lemma KS_bhaA0_ok : BG.kept_ok 64 PbhaA0.regs0 PbhaA0.regs_out0 KS_bhaA0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bhaA0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) ->
  140735332487360 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> L5.img_clear M 1249280 1282048 ->
  L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xa7fa4 M) (st fx' R' 0x5e0dc M')
        /\ (forall x, In x KS_bhaA0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 688148
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 10) = Z_to_bv 64 1056
        /\ getr R' (reg 11) = Z_to_bv 64 1309752
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 22) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 2147450880
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G10 G11 pvzI4 K1 K2 K3 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 35%nat. }
  assert (HR: regs_ok E PbhaA0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbhaA0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbhaA0.kn0).
  { unfold know_ok, PbhaA0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbhaA0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbhaA0.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 128) <= bv_unsigned a < (vz_2 - 128) + 128) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbhaA0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbhaA0.ps0) with 0x5e0dc in Hms. change (SR.ps_regs PbhaA0.ps0) with (map (fun i => (i, nth i PbhaA0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbhaA0.ps0) with PbhaA0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbhaA0.regs0 PbhaA0.regs_out0 64 KS_bhaA0 KS_bhaA0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbhaA0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbhaA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaA0.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbhaA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaA0.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbhaA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaA0.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbhaA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaA0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbhaA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaA0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbhaA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaA0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbhaA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaA0.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbhaA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaA0.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbhaA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaA0.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbhaA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
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

(* [comment removed for export] *)
Module PbhaA16 := LibSegBa_bhaA16_b.
Definition KS_bhaA16 : list nat := Eval vm_compute in (BG.kept_list 64 PbhaA16.regs0 PbhaA16.regs_out0).
Lemma KS_bhaA16_ok : BG.kept_ok 64 PbhaA16.regs0 PbhaA16.regs_out0 KS_bhaA16 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bhaA16_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) + 16) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) ->
  140735332487360 <= (V 2%nat) <= 140737488355312 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 144 -> L5.img_clear M 1249280 1282048 ->
  L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 144) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 144) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xa7fa4 M) (st fx' R' 0x5e0dc M')
        /\ (forall x, In x KS_bhaA16 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 688148
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) + 16)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 10) = Z_to_bv 64 1056
        /\ getr R' (reg 11) = Z_to_bv 64 1309752
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 22) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (bv_unsigned (getr R (reg 26)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 25)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' (V 2%nat) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 8) (bv_unsigned (getr R (reg 1)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G10 G11 pvzI4 K1 K2 K3 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 35%nat. }
  assert (HR: regs_ok E PbhaA16.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbhaA16.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbhaA16.kn0).
  { unfold know_ok, PbhaA16.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbhaA16.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbhaA16.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 128) <= bv_unsigned a < (vz_2 - 128) + 144) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbhaA16.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbhaA16.ps0) with 0x5e0dc in Hms. change (SR.ps_regs PbhaA16.ps0) with (map (fun i => (i, nth i PbhaA16.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbhaA16.ps0) with PbhaA16.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbhaA16.regs0 PbhaA16.regs_out0 64 KS_bhaA16 KS_bhaA16_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbhaA16.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbhaA16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaA16.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbhaA16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaA16.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbhaA16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaA16.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbhaA16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaA16.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbhaA16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaA16.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbhaA16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaA16.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbhaA16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaA16.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbhaA16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaA16.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbhaA16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaA16.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbhaA16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
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

(* [comment removed for export] *)
Module PbhaB := LibSegBa_bhaB_b.
Definition KS_bhaB : list nat := Eval vm_compute in (BG.kept_list 64 PbhaB.regs0 PbhaB.regs_out0).
Lemma KS_bhaB_ok : BG.kept_ok 64 PbhaB.regs0 PbhaB.regs_out0 KS_bhaB = true. Proof. vm_compute. reflexivity. Qed.
Lemma bhaB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 40%nat) -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 (V 33%nat) -> getr R (reg 25) = Z_to_bv 64 2147450880 ->
  140735332487360 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> L5.img_clear M 1249280 1282048 ->
  L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 4096 <= (V 40%nat) <= 140737488353280 -> aligned (V 40%nat) 32 ->
  L5.defined M (V 40%nat) 2048 -> L5.writable RSEGS M (V 40%nat) 2048 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 2048 <= 2147446784) -> L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 256 ->
  L5KA.zeros_at M (((V 40%nat) / 8) + 2147450880) 256 -> L5.u64_at RSEGS M ((V 40%nat) + 2040) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) -> ((V 40%nat) + 2048 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 128) + 144 <= (V 40%nat) \/ (V 40%nat) + 2048 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 144 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 128)) ->
  (65536 + 6840320 <= (V 40%nat) \/ (V 40%nat) + 2048 <= 65536) -> (65536 + 6840320 <= (V 41%nat) \/ (V 41%nat) + 1 <= 65536) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 112) <= bv_unsigned a < ((V 2%nat) - 112) + 8) -> ~ (((V 40%nat) + 0) <= bv_unsigned a < ((V 40%nat) + 0) + 24) -> ~ ((((V 40%nat) / 8) + 2147450880) <= bv_unsigned a < (((V 40%nat) / 8) + 2147450880) + 132) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 112) <= i < ((V 2%nat) - 112) + 8) -> ~ (((V 40%nat) + 0) <= i < ((V 40%nat) + 0) + 24) -> ~ ((((V 40%nat) / 8) + 2147450880) <= i < (((V 40%nat) / 8) + 2147450880) + 132) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xa8014 M) (st fx' R' 0xa8a0c M')
        /\ (forall x, In x KS_bhaB -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 688812
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 40%nat) + 32)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 688036
        /\ getr R' (reg 14) = Z_to_bv 64 18446744073709551601
        /\ getr R' (reg 18) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880)
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 40%nat) + 32)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 40%nat) + 96)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 40%nat)
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147451011) 243
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147451010) 243
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147451009) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147451008) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450987) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450986) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450985) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450984) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450979) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450978) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450977) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450976) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450983) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450982) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450981) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450980) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450971) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450970) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450969) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450968) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450975) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450974) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450973) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450972) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450963) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450962) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450961) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450960) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450967) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450966) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450965) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450964) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450955) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450954) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450953) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450952) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450959) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450958) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450957) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450956) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450947) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450946) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450945) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450944) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450951) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450950) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450949) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450948) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450939) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450938) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450937) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450936) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147451003) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147451002) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147451001) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147451000) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147451007) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147451006) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147451005) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147451004) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450995) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450994) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450993) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450992) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450999) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450998) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450997) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450996) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450991) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450990) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450989) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450988) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450943) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450942) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450941) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450940) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450931) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450930) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450929) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450928) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450935) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450934) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450933) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450932) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450923) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450922) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450921) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450920) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450927) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450926) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450925) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450924) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450915) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450914) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450913) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450912) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450919) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450918) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450917) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450916) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450907) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450906) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450905) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450904) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450911) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450910) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450909) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450908) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450899) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450898) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450897) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450896) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450903) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450902) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450901) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450900) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450891) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450890) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450889) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450888) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450895) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450894) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450893) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450892) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450887) 242
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450886) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450885) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450884) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450883) 241
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450882) 241
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450881) 241
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450880) 241
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 16) 688036
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 8) 129226
        /\ L5.u64_at RSEGS M' (V 40%nat) 1102416563
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 40%nat)
        /\ L5.defined M' ((V 40%nat) + 24) 2024
        /\ L5KA.zeros_at M' (((V 40%nat) / 8) + 2147451012) 124).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G1 G2 G9 G10 G22 G23 G25 pvzI7 K1 K2 K3 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 pvzI9 K15 K16 K17 K18 K19 K20 K21.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV40l; move HV40l before pvzI4; pose proof (proj2 pvzI4) as HV40r; move HV40r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV41l; move HV41l before pvzI5; pose proof (proj2 pvzI5) as HV41r; move HV41r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV58l; move HV58l before pvzI6; pose proof (proj2 pvzI6) as HV58r; move HV58r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_58 := V 58%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 58%nat => Z_to_bv 64 vz_58 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 40%nat => vz_40 | 41%nat => vz_41 | 58%nat => vz_58 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 59%nat. }
  assert (HR: regs_ok E PbhaB.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbhaB.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbhaB.kn0).
  { unfold know_ok, PbhaB.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K18 K19) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K18 K19) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K18 K19) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K18 K19; lia | clear - HV2l HV2r K0l K0r K18 K19; lia | clear - HV2l HV2r K0l K0r K18 K19; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K17 K18 K20; lia | clear - HV40l HV40r K6l K6r K10 K17 K18 K20; lia | clear - HV40l HV40r K6l K6r K10 K17 K18 K20; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K17 K18 K20; lia | clear - HV40l HV40r K6l K6r K10 K17 K18 K20; lia | clear - HV40l HV40r K6l K6r K10 K17 K18 K20; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K17 K18 K20; lia | clear - HV40l HV40r K6l K6r K10 K17 K18 K20; lia | clear - HV40l HV40r K6l K6r K10 K17 K18 K20; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K17 K18 K20; lia | clear - HV40l HV40r K6l K6r K10 K17 K18 K20; lia | clear - HV40l HV40r K6l K6r K10 K17 K18 K20; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17 K19 K21) | clear - HV40l HV40r K6l K6r K10 K17 K18 K20; lia | clear - HV40l HV40r K6l K6r K10 K17 K18 K20; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17 K19 K21) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K14l K14r K16 K17 K19 K21; lia | clear - HV41l HV41r K14l K14r K16 K17 K19 K21; lia | clear - HV41l HV41r K14l K14r K16 K17 K19 K21; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K18 K19) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K18 K19) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K16 K17 K19 K21) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbhaB.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbhaB.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 112) <= bv_unsigned a < (vz_2 - 112) + 8) -> ~ ((vz_40 + 0) <= bv_unsigned a < (vz_40 + 0) + 24) -> ~ (((vz_40 / 8) + 2147450880) <= bv_unsigned a < ((vz_40 / 8) + 2147450880) + 132) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PbhaB.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K18 K19) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K18 K19 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K17 K18 K20 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K17 K18 K20 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbhaB.ps0) with 0xa8a0c in Hms. change (SR.ps_regs PbhaB.ps0) with (map (fun i => (i, nth i PbhaB.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbhaB.ps0) with PbhaB.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbhaB.regs0 PbhaB.regs_out0 64 KS_bhaB KS_bhaB_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbhaB.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbhaB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaB.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbhaB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaB.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbhaB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaB.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbhaB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaB.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbhaB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaB.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbhaB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaB.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbhaB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaB.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbhaB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaB.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbhaB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaB.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbhaB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaB.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbhaB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 23%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 24%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 25%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 26%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 27%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 28%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 29%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 30%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 31%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 32%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 33%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 34%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 35%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 36%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 37%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 38%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 39%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 40%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 41%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 42%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 43%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 44%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 45%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 46%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 47%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 48%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 49%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 50%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 51%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 52%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 53%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 54%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 55%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 56%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 57%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 58%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 59%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 60%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 61%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 62%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 63%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 64%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 65%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 66%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 67%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 68%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 69%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 70%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 71%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 72%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 73%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 74%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 75%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 76%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 77%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 78%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 79%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 80%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 81%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 82%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 83%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 84%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 85%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 86%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 87%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 88%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 89%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 90%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 91%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 92%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 93%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 94%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 95%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 96%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 97%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 98%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 99%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 100%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 101%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 102%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 103%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 104%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 105%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 106%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 107%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 108%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 109%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 110%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 111%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 112%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 113%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 114%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 115%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 116%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 117%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 118%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 119%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 120%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 121%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 122%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 123%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 124%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 125%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 126%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 127%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 128%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 129%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 130%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 131%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 132%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 133%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 134%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 135%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K18 K19) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 136%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply zeros_of_KZeroa; [apply Hcells; apply (nth_error_In _ 137%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K17 K18 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

End PNAHP1.
