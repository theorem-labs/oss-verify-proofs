(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BigLinkZA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Ea0PlanKit AsanPlanCore
     BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.seg Require BndP_Ea_060S8 BndP_Ea_064S8 BndP_Ea_066S8 BndP_Ea_067S8.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PECVALARP1.
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

Module PavrE := BndP_Ea_060S8.LibSegEa_avrE.
Definition KS_avrE_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrE.regs0 PavrE.regs_out0).
Lemma KS_avrE_0_ok : BG.kept_ok 60 PavrE.regs0 PavrE.regs_out0 KS_avrE_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avrE_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrE.regs0 PavrE.regs_out1).
Lemma KS_avrE_1_ok : BG.kept_ok 60 PavrE.regs0 PavrE.regs_out1 KS_avrE_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrE_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 35%nat) ->
  L5.img_clear M 1253376 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487264 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 -> 0 <= (V 33%nat) <= 140737488355328 -> 0 <= (V 35%nat) <= 67108863 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 96) <= bv_unsigned a < ((V 2%nat) - 96) + 96) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 96) <= i < ((V 2%nat) - 96) + 96) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb5b60 M) (st fx' R' 0xb5e90 M')
        /\ (forall x, In x KS_avrE_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 96)
        /\ (((V 35%nat) - 0) mod 2 ^ 64) < 1
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
      \/ (msteps RSEGS (st fx R 0xb5b60 M) (st fx' R' 0xb5bec M')
        /\ (forall x, In x KS_avrE_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 96)
        /\ getr R' (reg 5) = Z_to_bv 64 245
        /\ getr R' (reg 6) = Z_to_bv 64 18446744073709551551
        /\ getr R' (reg 7) = Z_to_bv 64 239
        /\ getr R' (reg 8) = Z_to_bv 64 240
        /\ getr R' (reg 9) = Z_to_bv 64 144
        /\ getr R' (reg 11) = Z_to_bv 64 1317368
        /\ getr R' (reg 12) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat))
        /\ getr R' (reg 15) = Z_to_bv 64 8
        /\ getr R' (reg 16) = Z_to_bv 64 1
        /\ getr R' (reg 17) = Z_to_bv 64 18446744073709551554
        /\ getr R' (reg 18) = Z_to_bv 64 2147450880
        /\ getr R' (reg 19) = Z_to_bv 64 244
        /\ getr R' (reg 20) = Z_to_bv 64 143
        /\ getr R' (reg 21) = Z_to_bv 64 2
        /\ getr R' (reg 22) = Z_to_bv 64 3
        /\ getr R' (reg 28) = Z_to_bv 64 224
        /\ getr R' (reg 29) = Z_to_bv 64 160
        /\ getr R' (reg 30) = Z_to_bv 64 237
        /\ getr R' (reg 31) = Z_to_bv 64 159
        /\ 1 <= (((V 35%nat) - 0) mod 2 ^ 64)
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
  intros pvzI1 pvzI2 pvzI3 G2 G10 G11 K0 K1 K2 pvzI4 K4 K5 pvzI5 pvzI6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K3l; move K3l before pvzI4; pose proof (proj2 pvzI4) as K3r; move K3r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K6l; move K6l before pvzI5; pose proof (proj2 pvzI5) as K6r; move K6r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K7l; move K7l before pvzI6; pose proof (proj2 pvzI6) as K7r; move K7r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 36%nat. }
  assert (HR: regs_ok E PavrE.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrE.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrE.kn0).
  { unfold know_ok, PavrE.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrE.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrE.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 96) <= bv_unsigned a < (vz_2 - 96) + 96) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PavrE.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavrE.ps0) with 0xb5e90 in Hms. change (SR.ps_regs PavrE.ps0) with (map (fun i => (i, nth i PavrE.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrE.ps0) with PavrE.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrE.regs0 PavrE.regs_out0 60 KS_avrE_0 KS_avrE_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrE.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PavrE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
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
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
  - right.
    change (SR.ps_pc PavrE.ps1) with 0xb5bec in Hms. change (SR.ps_regs PavrE.ps1) with (map (fun i => (i, nth i PavrE.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrE.ps1) with PavrE.cells1 in Hcells. unfold PavrE.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrE.regs0 PavrE.regs_out1 60 KS_avrE_1 KS_avrE_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrE.regs_out1 E' R' 2 Hregs) by (clear; lia). cbn [nth PavrE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrE.regs_out1 E' R' 5 Hregs) by (clear; lia). cbn [nth PavrE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrE.regs_out1 E' R' 6 Hregs) by (clear; lia). cbn [nth PavrE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrE.regs_out1 E' R' 7 Hregs) by (clear; lia). cbn [nth PavrE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrE.regs_out1 E' R' 8 Hregs) by (clear; lia). cbn [nth PavrE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrE.regs_out1 E' R' 9 Hregs) by (clear; lia). cbn [nth PavrE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrE.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrE.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PavrE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrE.regs_out1 E' R' 14 Hregs) by (clear; lia). cbn [nth PavrE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrE.regs_out1 E' R' 15 Hregs) by (clear; lia). cbn [nth PavrE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrE.regs_out1 E' R' 16 Hregs) by (clear; lia). cbn [nth PavrE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrE.regs_out1 E' R' 17 Hregs) by (clear; lia). cbn [nth PavrE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrE.regs_out1 E' R' 18 Hregs) by (clear; lia). cbn [nth PavrE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrE.regs_out1 E' R' 19 Hregs) by (clear; lia). cbn [nth PavrE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrE.regs_out1 E' R' 20 Hregs) by (clear; lia). cbn [nth PavrE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrE.regs_out1 E' R' 21 Hregs) by (clear; lia). cbn [nth PavrE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrE.regs_out1 E' R' 22 Hregs) by (clear; lia). cbn [nth PavrE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrE.regs_out1 E' R' 28 Hregs) by (clear; lia). cbn [nth PavrE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrE.regs_out1 E' R' 29 Hregs) by (clear; lia). cbn [nth PavrE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrE.regs_out1 E' R' 30 Hregs) by (clear; lia). cbn [nth PavrE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrE.regs_out1 E' R' 31 Hregs) by (clear; lia). cbn [nth PavrE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
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
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PavrHf := BndP_Ea_064S8.LibSegEa_avrHf.
Definition KS_avrHf_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrHf.regs0 PavrHf.regs_out0).
Lemma KS_avrHf_0_ok : BG.kept_ok 60 PavrHf.regs0 PavrHf.regs_out0 KS_avrHf_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avrHf_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrHf.regs0 PavrHf.regs_out1).
Lemma KS_avrHf_1_ok : BG.kept_ok 60 PavrHf.regs0 PavrHf.regs_out1 KS_avrHf_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrHf_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M (V 33%nat) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb5bec M) (st fx' R' 0xb5cdc M')
        /\ (forall x, In x KS_avrHf_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb5bec M) (st fx' R' 0xb5c0c M')
        /\ (forall x, In x KS_avrHf_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G12 G14 G15 G16 G17 G18 G19 G20 G21 G22 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavrHf.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrHf.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrHf.kn0).
  { unfold know_ok, PavrHf.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrHf.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrHf.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavrHf.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavrHf.ps0) with 0xb5cdc in Hms. change (SR.ps_regs PavrHf.ps0) with (map (fun i => (i, nth i PavrHf.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrHf.ps0) with PavrHf.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrHf.regs0 PavrHf.regs_out0 60 KS_avrHf_0 KS_avrHf_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrHf.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrHf.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrHf.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrHf.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  - right.
    change (SR.ps_pc PavrHf.ps1) with 0xb5c0c in Hms. change (SR.ps_regs PavrHf.ps1) with (map (fun i => (i, nth i PavrHf.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrHf.ps1) with PavrHf.cells1 in Hcells. unfold PavrHf.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrHf.regs0 PavrHf.regs_out1 60 KS_avrHf_1 KS_avrHf_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrHf.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrHf.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrHf.regs_out1 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrHf.regs_out1]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
Qed.

Module PavrHsZ := BndP_Ea_064S8.LibSegEa_avrHsZ.
Definition KS_avrHsZ : list nat := Eval vm_compute in (BG.kept_list 60 PavrHsZ.regs0 PavrHsZ.regs_out0).
Lemma KS_avrHsZ_ok : BG.kept_ok 60 PavrHsZ.regs0 PavrHsZ.regs_out0 KS_avrHsZ = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrHsZ_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 7 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M (V 33%nat) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5bec M) (st fx' R' 0xb5cdc M')
        /\ (forall x, In x KS_avrHsZ -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G12 G14 G15 G16 G17 G18 G19 G20 G21 G22 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavrHsZ.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrHsZ.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrHsZ.kn0).
  { unfold know_ok, PavrHsZ.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrHsZ.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrHsZ.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavrHsZ.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PavrHsZ.ps0) with 0xb5cdc in Hms. change (SR.ps_regs PavrHsZ.ps0) with (map (fun i => (i, nth i PavrHsZ.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PavrHsZ.ps0) with PavrHsZ.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrHsZ.regs0 PavrHsZ.regs_out0 60 KS_avrHsZ KS_avrHsZ_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PavrHsZ.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrHsZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PavrHsZ.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrHsZ.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity.
Qed.

Module PavrHsP1 := BndP_Ea_064S8.LibSegEa_avrHsP1.
Definition KS_avrHsP1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrHsP1.regs0 PavrHsP1.regs_out0).
Lemma KS_avrHsP1_ok : BG.kept_ok 60 PavrHsP1.regs0 PavrHsP1.regs_out0 KS_avrHsP1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrHsP1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 7 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M (V 33%nat) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M (((V 33%nat) / 8) + 2147450880) 1 -> 0 <= Z.land (V 33%nat) 7 <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5bec M) (st fx' R' 0xb5cdc M')
        /\ (forall x, In x KS_avrHsP1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G12 G14 G15 G16 G17 G18 G19 G20 G21 G22 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 pvzI9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavrHsP1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrHsP1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrHsP1.kn0).
  { unfold know_ok, PavrHsP1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | clear; lia | exact (conj K6l K6r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrHsP1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrHsP1.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavrHsP1.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PavrHsP1.ps0) with 0xb5cdc in Hms. change (SR.ps_regs PavrHsP1.ps0) with (map (fun i => (i, nth i PavrHsP1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PavrHsP1.ps0) with PavrHsP1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrHsP1.regs0 PavrHsP1.regs_out0 60 KS_avrHsP1 KS_avrHsP1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PavrHsP1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrHsP1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavrHsP1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrHsP1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PavrHsP1.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrHsP1.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity.
Qed.

Module PavrHsP2 := BndP_Ea_064S8.LibSegEa_avrHsP2.
Definition KS_avrHsP2 : list nat := Eval vm_compute in (BG.kept_list 60 PavrHsP2.regs0 PavrHsP2.regs_out0).
Lemma KS_avrHsP2_ok : BG.kept_ok 60 PavrHsP2.regs0 PavrHsP2.regs_out0 KS_avrHsP2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrHsP2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 7 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M (V 33%nat) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M (((V 33%nat) / 8) + 2147450880) 2 -> 0 <= Z.land (V 33%nat) 7 <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5bec M) (st fx' R' 0xb5cdc M')
        /\ (forall x, In x KS_avrHsP2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ bv_unsigned (getr R' (reg 11)) = (Z.land (V 33%nat) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G12 G14 G15 G16 G17 G18 G19 G20 G21 G22 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 pvzI9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavrHsP2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrHsP2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrHsP2.kn0).
  { unfold know_ok, PavrHsP2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | clear; lia | exact (conj K6l K6r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrHsP2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrHsP2.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavrHsP2.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PavrHsP2.ps0) with 0xb5cdc in Hms. change (SR.ps_regs PavrHsP2.ps0) with (map (fun i => (i, nth i PavrHsP2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PavrHsP2.ps0) with PavrHsP2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrHsP2.regs0 PavrHsP2.regs_out0 60 KS_avrHsP2 KS_avrHsP2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PavrHsP2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrHsP2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavrHsP2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrHsP2.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
  rewrite (BG.out_reg PavrHsP2.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrHsP2.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity.
Qed.

Module PavrHsP3 := BndP_Ea_064S8.LibSegEa_avrHsP3.
Definition KS_avrHsP3 : list nat := Eval vm_compute in (BG.kept_list 60 PavrHsP3.regs0 PavrHsP3.regs_out0).
Lemma KS_avrHsP3_ok : BG.kept_ok 60 PavrHsP3.regs0 PavrHsP3.regs_out0 KS_avrHsP3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrHsP3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 7 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M (V 33%nat) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M (((V 33%nat) / 8) + 2147450880) 3 -> 0 <= Z.land (V 33%nat) 7 <= 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5bec M) (st fx' R' 0xb5cdc M')
        /\ (forall x, In x KS_avrHsP3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ bv_unsigned (getr R' (reg 11)) = (Z.land (V 33%nat) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G12 G14 G15 G16 G17 G18 G19 G20 G21 G22 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 pvzI9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavrHsP3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrHsP3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrHsP3.kn0).
  { unfold know_ok, PavrHsP3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | clear; lia | exact (conj K6l K6r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrHsP3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrHsP3.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavrHsP3.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PavrHsP3.ps0) with 0xb5cdc in Hms. change (SR.ps_regs PavrHsP3.ps0) with (map (fun i => (i, nth i PavrHsP3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PavrHsP3.ps0) with PavrHsP3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrHsP3.regs0 PavrHsP3.regs_out0 60 KS_avrHsP3 KS_avrHsP3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PavrHsP3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrHsP3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavrHsP3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrHsP3.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
  rewrite (BG.out_reg PavrHsP3.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrHsP3.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity.
Qed.

Module PavrHsP4 := BndP_Ea_064S8.LibSegEa_avrHsP4.
Definition KS_avrHsP4 : list nat := Eval vm_compute in (BG.kept_list 60 PavrHsP4.regs0 PavrHsP4.regs_out0).
Lemma KS_avrHsP4_ok : BG.kept_ok 60 PavrHsP4.regs0 PavrHsP4.regs_out0 KS_avrHsP4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrHsP4_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 7 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M (V 33%nat) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M (((V 33%nat) / 8) + 2147450880) 4 -> 0 <= Z.land (V 33%nat) 7 <= 3 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5bec M) (st fx' R' 0xb5cdc M')
        /\ (forall x, In x KS_avrHsP4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ bv_unsigned (getr R' (reg 11)) = (Z.land (V 33%nat) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G12 G14 G15 G16 G17 G18 G19 G20 G21 G22 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 pvzI9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavrHsP4.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrHsP4.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrHsP4.kn0).
  { unfold know_ok, PavrHsP4.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | clear; lia | exact (conj K6l K6r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrHsP4.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrHsP4.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavrHsP4.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PavrHsP4.ps0) with 0xb5cdc in Hms. change (SR.ps_regs PavrHsP4.ps0) with (map (fun i => (i, nth i PavrHsP4.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PavrHsP4.ps0) with PavrHsP4.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrHsP4.regs0 PavrHsP4.regs_out0 60 KS_avrHsP4 KS_avrHsP4_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PavrHsP4.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrHsP4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavrHsP4.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrHsP4.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
  rewrite (BG.out_reg PavrHsP4.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrHsP4.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity.
Qed.

Module PavrHsP5 := BndP_Ea_064S8.LibSegEa_avrHsP5.
Definition KS_avrHsP5 : list nat := Eval vm_compute in (BG.kept_list 60 PavrHsP5.regs0 PavrHsP5.regs_out0).
Lemma KS_avrHsP5_ok : BG.kept_ok 60 PavrHsP5.regs0 PavrHsP5.regs_out0 KS_avrHsP5 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrHsP5_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 7 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M (V 33%nat) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M (((V 33%nat) / 8) + 2147450880) 5 -> 0 <= Z.land (V 33%nat) 7 <= 4 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5bec M) (st fx' R' 0xb5cdc M')
        /\ (forall x, In x KS_avrHsP5 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ bv_unsigned (getr R' (reg 11)) = (Z.land (V 33%nat) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G12 G14 G15 G16 G17 G18 G19 G20 G21 G22 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 pvzI9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavrHsP5.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrHsP5.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrHsP5.kn0).
  { unfold know_ok, PavrHsP5.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | clear; lia | exact (conj K6l K6r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrHsP5.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrHsP5.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavrHsP5.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PavrHsP5.ps0) with 0xb5cdc in Hms. change (SR.ps_regs PavrHsP5.ps0) with (map (fun i => (i, nth i PavrHsP5.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PavrHsP5.ps0) with PavrHsP5.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrHsP5.regs0 PavrHsP5.regs_out0 60 KS_avrHsP5 KS_avrHsP5_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PavrHsP5.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrHsP5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavrHsP5.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrHsP5.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
  rewrite (BG.out_reg PavrHsP5.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrHsP5.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity.
Qed.

Module PavrHsP6 := BndP_Ea_064S8.LibSegEa_avrHsP6.
Definition KS_avrHsP6 : list nat := Eval vm_compute in (BG.kept_list 60 PavrHsP6.regs0 PavrHsP6.regs_out0).
Lemma KS_avrHsP6_ok : BG.kept_ok 60 PavrHsP6.regs0 PavrHsP6.regs_out0 KS_avrHsP6 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrHsP6_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 7 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M (V 33%nat) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M (((V 33%nat) / 8) + 2147450880) 6 -> 0 <= Z.land (V 33%nat) 7 <= 5 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5bec M) (st fx' R' 0xb5cdc M')
        /\ (forall x, In x KS_avrHsP6 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ bv_unsigned (getr R' (reg 11)) = (Z.land (V 33%nat) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G12 G14 G15 G16 G17 G18 G19 G20 G21 G22 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 pvzI9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavrHsP6.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrHsP6.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrHsP6.kn0).
  { unfold know_ok, PavrHsP6.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | clear; lia | exact (conj K6l K6r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrHsP6.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrHsP6.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavrHsP6.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PavrHsP6.ps0) with 0xb5cdc in Hms. change (SR.ps_regs PavrHsP6.ps0) with (map (fun i => (i, nth i PavrHsP6.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PavrHsP6.ps0) with PavrHsP6.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrHsP6.regs0 PavrHsP6.regs_out0 60 KS_avrHsP6 KS_avrHsP6_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PavrHsP6.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrHsP6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavrHsP6.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrHsP6.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
  rewrite (BG.out_reg PavrHsP6.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrHsP6.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity.
Qed.

Module PavrHsP7 := BndP_Ea_064S8.LibSegEa_avrHsP7.
Definition KS_avrHsP7 : list nat := Eval vm_compute in (BG.kept_list 60 PavrHsP7.regs0 PavrHsP7.regs_out0).
Lemma KS_avrHsP7_ok : BG.kept_ok 60 PavrHsP7.regs0 PavrHsP7.regs_out0 KS_avrHsP7 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrHsP7_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 7 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M (V 33%nat) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M (((V 33%nat) / 8) + 2147450880) 7 -> 0 <= Z.land (V 33%nat) 7 <= 6 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5bec M) (st fx' R' 0xb5cdc M')
        /\ (forall x, In x KS_avrHsP7 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ bv_unsigned (getr R' (reg 11)) = (Z.land (V 33%nat) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G12 G14 G15 G16 G17 G18 G19 G20 G21 G22 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 pvzI9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavrHsP7.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrHsP7.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrHsP7.kn0).
  { unfold know_ok, PavrHsP7.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | clear - HV33l HV33r K0l K0r K2l K2r K6l K6r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r K6l K6r) | clear; lia | exact (conj K6l K6r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrHsP7.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrHsP7.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavrHsP7.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PavrHsP7.ps0) with 0xb5cdc in Hms. change (SR.ps_regs PavrHsP7.ps0) with (map (fun i => (i, nth i PavrHsP7.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PavrHsP7.ps0) with PavrHsP7.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrHsP7.regs0 PavrHsP7.regs_out0 60 KS_avrHsP7 KS_avrHsP7_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PavrHsP7.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrHsP7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavrHsP7.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrHsP7.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
  rewrite (BG.out_reg PavrHsP7.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrHsP7.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity.
Qed.

Module PavrS := BndP_Ea_066S8.LibSegEa_avrS.
Definition KS_avrS : list nat := Eval vm_compute in (BG.kept_list 60 PavrS.regs0 PavrS.regs_out0).
Lemma KS_avrS_ok : BG.kept_ok 60 PavrS.regs0 PavrS.regs_out0 KS_avrS = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 23) = Z_to_bv 64 (V 36%nat) -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5KA.zeros_at M 2147469107 33 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5cdc M) (st fx' R' 0xb5cfc M')
        /\ (forall x, In x KS_avrS -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 11)) = (((Z.land (V 36%nat) 255) + 145821) mod 2 ^ 64)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ bv_unsigned (getr R' (reg 24)) = (Z.land (V 36%nat) 255)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G10 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavrS.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrS.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrS.kn0).
  { unfold know_ok, PavrS.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K3]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrS.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrS.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavrS.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PavrS.ps0) with 0xb5cfc in Hms. change (SR.ps_regs PavrS.ps0) with (map (fun i => (i, nth i PavrS.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PavrS.ps0) with PavrS.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrS.regs0 PavrS.regs_out0 60 KS_avrS KS_avrS_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PavrS.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrS.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
  split. { rewrite (BG.out_reg PavrS.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavrS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PavrS.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PavrS.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac.
Qed.

Module PavrT0 := BndP_Ea_066S8.LibSegEa_avrT0.
Definition KS_avrT0_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrT0.regs0 PavrT0.regs_out0).
Lemma KS_avrT0_0_ok : BG.kept_ok 60 PavrT0.regs0 PavrT0.regs_out0 KS_avrT0_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avrT0_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrT0.regs0 PavrT0.regs_out1).
Lemma KS_avrT0_1_ok : BG.kept_ok 60 PavrT0.regs0 PavrT0.regs_out1 KS_avrT0_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avrT0_2 : list nat := Eval vm_compute in (BG.kept_list 60 PavrT0.regs0 PavrT0.regs_out2).
Lemma KS_avrT0_2_ok : BG.kept_ok 60 PavrT0.regs0 PavrT0.regs_out2 KS_avrT0_2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrT0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 23) = Z_to_bv 64 (V 36%nat) -> getr R (reg 24) = Z_to_bv 64 (V 37%nat) -> getr R (reg 25) = Z_to_bv 64 0 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb5d00 M) (st fx' R' 0xb5e90 M')
        /\ (forall x, In x KS_avrT0_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 13) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 36)) (ELit 56))
        /\ bv_unsigned (getr R' (reg 23)) = ((72057594037927936 * (V 36%nat)) mod 2 ^ 64)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 36)) (ELit 56)) (ELit (-62)))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb5d00 M) (st fx' R' 0xb5dd4 M')
        /\ (forall x, In x KS_avrT0_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 13) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 36)) (ELit 56))
        /\ bv_unsigned (getr R' (reg 23)) = ((72057594037927936 * (V 36%nat)) mod 2 ^ 64)
        /\ (V 37%nat) < 245
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 36)) (ELit 56)) (ELit (-62)))) <= 0)
      \/ (msteps RSEGS (st fx R 0xb5d00 M) (st fx' R' 0xb5e90 M')
        /\ (forall x, In x KS_avrT0_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 13) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 36)) (ELit 56))
        /\ bv_unsigned (getr R' (reg 23)) = ((72057594037927936 * (V 36%nat)) mod 2 ^ 64)
        /\ 245 <= (V 37%nat)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 36)) (ELit 56)) (ELit (-62)))) <= 0)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G5 G6 G7 G8 G9 G10 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G25 G28 G29 G30 G31 pvzI6 pvzI7 pvzI8 pvzI9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K1l; move K1l before pvzI7; pose proof (proj2 pvzI7) as K1r; move K1r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K2l; move K2l before pvzI8; pose proof (proj2 pvzI8) as K2r; move K2r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PavrT0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrT0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrT0.kn0).
  { unfold know_ok, PavrT0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrT0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrT0.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavrT0.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PavrT0.ps0) with 0xb5e90 in Hms. change (SR.ps_regs PavrT0.ps0) with (map (fun i => (i, nth i PavrT0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrT0.ps0) with PavrT0.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrT0.regs0 PavrT0.regs_out0 60 KS_avrT0_0 KS_avrT0_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrT0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrT0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrT0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavrT0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrT0.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrT0.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    split. { rewrite (BG.out_reg PavrT0.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrT0.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. left.
    change (SR.ps_pc PavrT0.ps1) with 0xb5dd4 in Hms. change (SR.ps_regs PavrT0.ps1) with (map (fun i => (i, nth i PavrT0.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrT0.ps1) with PavrT0.cells1 in Hcells. unfold PavrT0.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrT0.regs0 PavrT0.regs_out1 60 KS_avrT0_1 KS_avrT0_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrT0.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrT0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrT0.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PavrT0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrT0.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrT0.regs_out1]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    split. { rewrite (BG.out_reg PavrT0.regs_out1 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrT0.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right.
    change (SR.ps_pc PavrT0.ps2) with 0xb5e90 in Hms. change (SR.ps_regs PavrT0.ps2) with (map (fun i => (i, nth i PavrT0.regs_out2 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrT0.ps2) with PavrT0.cells2 in Hcells. unfold PavrT0.cells2 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrT0.regs0 PavrT0.regs_out2 60 KS_avrT0_2 KS_avrT0_2_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrT0.regs_out2 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrT0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrT0.regs_out2 E' R' 12 Hregs) by (clear; lia). cbn [nth PavrT0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrT0.regs_out2 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrT0.regs_out2]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    split. { rewrite (BG.out_reg PavrT0.regs_out2 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrT0.regs_out2]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.

Module PavrT1a := BndP_Ea_066S8.LibSegEa_avrT1a.
Definition KS_avrT1a : list nat := Eval vm_compute in (BG.kept_list 60 PavrT1a.regs0 PavrT1a.regs_out0).
Lemma KS_avrT1a_ok : BG.kept_ok 60 PavrT1a.regs0 PavrT1a.regs_out0 KS_avrT1a = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrT1a_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 23) = Z_to_bv 64 (V 36%nat) -> getr R (reg 24) = Z_to_bv 64 (V 37%nat) -> getr R (reg 25) = Z_to_bv 64 1 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 1 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5d00 M) (st fx' R' 0xb5e90 M')
        /\ (forall x, In x KS_avrT1a -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 5).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G5 G6 G7 G8 G9 G10 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G25 G28 G29 G30 G31 pvzI6 pvzI7 pvzI8 pvzI9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K1l; move K1l before pvzI7; pose proof (proj2 pvzI7) as K1r; move K1r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K2l; move K2l before pvzI8; pose proof (proj2 pvzI8) as K2r; move K2r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PavrT1a.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrT1a.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrT1a.kn0).
  { unfold know_ok, PavrT1a.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrT1a.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrT1a.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavrT1a.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PavrT1a.ps0) with 0xb5e90 in Hms. change (SR.ps_regs PavrT1a.ps0) with (map (fun i => (i, nth i PavrT1a.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PavrT1a.ps0) with PavrT1a.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrT1a.regs0 PavrT1a.regs_out0 60 KS_avrT1a KS_avrT1a_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg PavrT1a.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrT1a.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PavrT1b := BndP_Ea_066S8.LibSegEa_avrT1b.
Definition KS_avrT1b : list nat := Eval vm_compute in (BG.kept_list 60 PavrT1b.regs0 PavrT1b.regs_out0).
Lemma KS_avrT1b_ok : BG.kept_ok 60 PavrT1b.regs0 PavrT1b.regs_out0 KS_avrT1b = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrT1b_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 23) = Z_to_bv 64 (V 36%nat) -> getr R (reg 24) = Z_to_bv 64 (V 37%nat) -> getr R (reg 25) = Z_to_bv 64 1 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 2 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5d00 M) (st fx' R' 0xb5d6c M')
        /\ (forall x, In x KS_avrT1b -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 2)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G5 G6 G7 G8 G9 G10 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G25 G28 G29 G30 G31 pvzI6 pvzI7 pvzI8 pvzI9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K1l; move K1l before pvzI7; pose proof (proj2 pvzI7) as K1r; move K1r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K2l; move K2l before pvzI8; pose proof (proj2 pvzI8) as K2r; move K2r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PavrT1b.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrT1b.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrT1b.kn0).
  { unfold know_ok, PavrT1b.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrT1b.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrT1b.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavrT1b.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PavrT1b.ps0) with 0xb5d6c in Hms. change (SR.ps_regs PavrT1b.ps0) with (map (fun i => (i, nth i PavrT1b.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PavrT1b.ps0) with PavrT1b.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrT1b.regs0 PavrT1b.regs_out0 60 KS_avrT1b KS_avrT1b_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PavrT1b.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrT1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavrT1b.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavrT1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PavrT1b.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrT1b.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PavrT2a := BndP_Ea_066S8.LibSegEa_avrT2a.
Definition KS_avrT2a : list nat := Eval vm_compute in (BG.kept_list 60 PavrT2a.regs0 PavrT2a.regs_out0).
Lemma KS_avrT2a_ok : BG.kept_ok 60 PavrT2a.regs0 PavrT2a.regs_out0 KS_avrT2a = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrT2a_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 23) = Z_to_bv 64 (V 36%nat) -> getr R (reg 24) = Z_to_bv 64 (V 37%nat) -> getr R (reg 25) = Z_to_bv 64 2 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 2 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5d00 M) (st fx' R' 0xb5e90 M')
        /\ (forall x, In x KS_avrT2a -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 5).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G5 G6 G7 G8 G9 G10 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G25 G28 G29 G30 G31 pvzI6 pvzI7 pvzI8 pvzI9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K1l; move K1l before pvzI7; pose proof (proj2 pvzI7) as K1r; move K1r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K2l; move K2l before pvzI8; pose proof (proj2 pvzI8) as K2r; move K2r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PavrT2a.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrT2a.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrT2a.kn0).
  { unfold know_ok, PavrT2a.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrT2a.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrT2a.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavrT2a.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PavrT2a.ps0) with 0xb5e90 in Hms. change (SR.ps_regs PavrT2a.ps0) with (map (fun i => (i, nth i PavrT2a.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PavrT2a.ps0) with PavrT2a.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrT2a.regs0 PavrT2a.regs_out0 60 KS_avrT2a KS_avrT2a_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg PavrT2a.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrT2a.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PavrT2b := BndP_Ea_066S8.LibSegEa_avrT2b.
Definition KS_avrT2b : list nat := Eval vm_compute in (BG.kept_list 60 PavrT2b.regs0 PavrT2b.regs_out0).
Lemma KS_avrT2b_ok : BG.kept_ok 60 PavrT2b.regs0 PavrT2b.regs_out0 KS_avrT2b = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrT2b_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 23) = Z_to_bv 64 (V 36%nat) -> getr R (reg 24) = Z_to_bv 64 (V 37%nat) -> getr R (reg 25) = Z_to_bv 64 2 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 3 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5d00 M) (st fx' R' 0xb5d50 M')
        /\ (forall x, In x KS_avrT2b -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 3)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G5 G6 G7 G8 G9 G10 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G25 G28 G29 G30 G31 pvzI6 pvzI7 pvzI8 pvzI9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K1l; move K1l before pvzI7; pose proof (proj2 pvzI7) as K1r; move K1r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K2l; move K2l before pvzI8; pose proof (proj2 pvzI8) as K2r; move K2r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PavrT2b.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrT2b.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrT2b.kn0).
  { unfold know_ok, PavrT2b.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrT2b.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrT2b.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavrT2b.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PavrT2b.ps0) with 0xb5d50 in Hms. change (SR.ps_regs PavrT2b.ps0) with (map (fun i => (i, nth i PavrT2b.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PavrT2b.ps0) with PavrT2b.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrT2b.regs0 PavrT2b.regs_out0 60 KS_avrT2b KS_avrT2b_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PavrT2b.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrT2b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavrT2b.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavrT2b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavrT2b.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrT2b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PavrT2b.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PavrT2b.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PavrT3a := BndP_Ea_067S8.LibSegEa_avrT3a.
Definition KS_avrT3a : list nat := Eval vm_compute in (BG.kept_list 60 PavrT3a.regs0 PavrT3a.regs_out0).
Lemma KS_avrT3a_ok : BG.kept_ok 60 PavrT3a.regs0 PavrT3a.regs_out0 KS_avrT3a = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrT3a_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 23) = Z_to_bv 64 (V 36%nat) -> getr R (reg 24) = Z_to_bv 64 (V 37%nat) -> getr R (reg 25) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 3 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5d00 M) (st fx' R' 0xb5e90 M')
        /\ (forall x, In x KS_avrT3a -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 5).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G5 G6 G7 G8 G9 G10 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G25 G28 G29 G30 G31 pvzI6 pvzI7 pvzI8 pvzI9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K1l; move K1l before pvzI7; pose proof (proj2 pvzI7) as K1r; move K1r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K2l; move K2l before pvzI8; pose proof (proj2 pvzI8) as K2r; move K2r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PavrT3a.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrT3a.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrT3a.kn0).
  { unfold know_ok, PavrT3a.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrT3a.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrT3a.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavrT3a.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PavrT3a.ps0) with 0xb5e90 in Hms. change (SR.ps_regs PavrT3a.ps0) with (map (fun i => (i, nth i PavrT3a.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PavrT3a.ps0) with PavrT3a.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrT3a.regs0 PavrT3a.regs_out0 60 KS_avrT3a KS_avrT3a_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg PavrT3a.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrT3a.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PavrT3b := BndP_Ea_067S8.LibSegEa_avrT3b.
Definition KS_avrT3b : list nat := Eval vm_compute in (BG.kept_list 60 PavrT3b.regs0 PavrT3b.regs_out0).
Lemma KS_avrT3b_ok : BG.kept_ok 60 PavrT3b.regs0 PavrT3b.regs_out0 KS_avrT3b = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrT3b_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 23) = Z_to_bv 64 (V 36%nat) -> getr R (reg 24) = Z_to_bv 64 (V 37%nat) -> getr R (reg 25) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 4 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5d00 M) (st fx' R' 0xb5d34 M')
        /\ (forall x, In x KS_avrT3b -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + 4)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 4)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G5 G6 G7 G8 G9 G10 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G25 G28 G29 G30 G31 pvzI6 pvzI7 pvzI8 pvzI9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K1l; move K1l before pvzI7; pose proof (proj2 pvzI7) as K1r; move K1r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K2l; move K2l before pvzI8; pose proof (proj2 pvzI8) as K2r; move K2r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PavrT3b.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrT3b.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrT3b.kn0).
  { unfold know_ok, PavrT3b.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrT3b.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrT3b.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavrT3b.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PavrT3b.ps0) with 0xb5d34 in Hms. change (SR.ps_regs PavrT3b.ps0) with (map (fun i => (i, nth i PavrT3b.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PavrT3b.ps0) with PavrT3b.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrT3b.regs0 PavrT3b.regs_out0 60 KS_avrT3b KS_avrT3b_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PavrT3b.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrT3b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavrT3b.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavrT3b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavrT3b.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrT3b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PavrT3b.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PavrT3b.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PavrTbig := BndP_Ea_067S8.LibSegEa_avrTbig.
Definition KS_avrTbig_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrTbig.regs0 PavrTbig.regs_out0).
Lemma KS_avrTbig_0_ok : BG.kept_ok 60 PavrTbig.regs0 PavrTbig.regs_out0 KS_avrTbig_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avrTbig_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrTbig.regs0 PavrTbig.regs_out1).
Lemma KS_avrTbig_1_ok : BG.kept_ok 60 PavrTbig.regs0 PavrTbig.regs_out1 KS_avrTbig_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrTbig_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 23) = Z_to_bv 64 (V 36%nat) -> getr R (reg 24) = Z_to_bv 64 (V 37%nat) -> getr R (reg 25) = Z_to_bv 64 (V 38%nat) -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  4 <= (V 38%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb5d00 M) (st fx' R' 0xb5e90 M')
        /\ (forall x, In x KS_avrTbig_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 (((V 33%nat) + (V 38%nat)) + 1)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 38%nat))
        /\ getr R' (reg 26) = Z_to_bv 64 (((V 33%nat) + (V 38%nat)) + 1)
        /\ (V 38%nat) < (V 35%nat))
      \/ (msteps RSEGS (st fx R 0xb5d00 M) (st fx' R' 0xb5e90 M')
        /\ (forall x, In x KS_avrTbig_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 5
        /\ (V 35%nat) <= (V 38%nat))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G5 G6 G7 G8 G9 G10 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G25 G28 G29 G30 G31 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K1l; move K1l before pvzI8; pose proof (proj2 pvzI8) as K1r; move K1r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K2l; move K2l before pvzI9; pose proof (proj2 pvzI9) as K2r; move K2r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K4l; move K4l before pvzI11; pose proof (proj2 pvzI11) as K4r; move K4r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 39%nat. }
  assert (HR: regs_ok E PavrTbig.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrTbig.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrTbig.kn0).
  { unfold know_ok, PavrTbig.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrTbig.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrTbig.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavrTbig.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavrTbig.ps0) with 0xb5e90 in Hms. change (SR.ps_regs PavrTbig.ps0) with (map (fun i => (i, nth i PavrTbig.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrTbig.ps0) with PavrTbig.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrTbig.regs0 PavrTbig.regs_out0 60 KS_avrTbig_0 KS_avrTbig_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrTbig.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrTbig.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrTbig.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavrTbig.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrTbig.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrTbig.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrTbig.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PavrTbig.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  - right.
    change (SR.ps_pc PavrTbig.ps1) with 0xb5e90 in Hms. change (SR.ps_regs PavrTbig.ps1) with (map (fun i => (i, nth i PavrTbig.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrTbig.ps1) with PavrTbig.cells1 in Hcells. unfold PavrTbig.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrTbig.regs0 PavrTbig.regs_out1 60 KS_avrTbig_1 KS_avrTbig_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrTbig.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrTbig.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
Qed.

Module PavrL := BndP_Ea_064S8.LibSegEa_avrL.
Definition KS_avrL_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrL.regs0 PavrL.regs_out0).
Lemma KS_avrL_0_ok : BG.kept_ok 60 PavrL.regs0 PavrL.regs_out0 KS_avrL_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avrL_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrL.regs0 PavrL.regs_out1).
Lemma KS_avrL_1_ok : BG.kept_ok 60 PavrL.regs0 PavrL.regs_out1 KS_avrL_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avrL_2 : list nat := Eval vm_compute in (BG.kept_list 60 PavrL.regs0 PavrL.regs_out2).
Lemma KS_avrL_2_ok : BG.kept_ok 60 PavrL.regs0 PavrL.regs_out2 KS_avrL_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avrL_3 : list nat := Eval vm_compute in (BG.kept_list 60 PavrL.regs0 PavrL.regs_out3).
Lemma KS_avrL_3_ok : BG.kept_ok 60 PavrL.regs0 PavrL.regs_out3 KS_avrL_3 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avrL_4 : list nat := Eval vm_compute in (BG.kept_list 60 PavrL.regs0 PavrL.regs_out4).
Lemma KS_avrL_4_ok : BG.kept_ok 60 PavrL.regs0 PavrL.regs_out4 KS_avrL_4 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avrL_5 : list nat := Eval vm_compute in (BG.kept_list 60 PavrL.regs0 PavrL.regs_out5).
Lemma KS_avrL_5_ok : BG.kept_ok 60 PavrL.regs0 PavrL.regs_out5 KS_avrL_5 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avrL_6 : list nat := Eval vm_compute in (BG.kept_list 60 PavrL.regs0 PavrL.regs_out6).
Lemma KS_avrL_6_ok : BG.kept_ok 60 PavrL.regs0 PavrL.regs_out6 KS_avrL_6 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avrL_7 : list nat := Eval vm_compute in (BG.kept_list 60 PavrL.regs0 PavrL.regs_out7).
Lemma KS_avrL_7_ok : BG.kept_ok 60 PavrL.regs0 PavrL.regs_out7 KS_avrL_7 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avrL_8 : list nat := Eval vm_compute in (BG.kept_list 60 PavrL.regs0 PavrL.regs_out8).
Lemma KS_avrL_8_ok : BG.kept_ok 60 PavrL.regs0 PavrL.regs_out8 KS_avrL_8 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avrL_9 : list nat := Eval vm_compute in (BG.kept_list 60 PavrL.regs0 PavrL.regs_out9).
Lemma KS_avrL_9_ok : BG.kept_ok 60 PavrL.regs0 PavrL.regs_out9 KS_avrL_9 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avrL_10 : list nat := Eval vm_compute in (BG.kept_list 60 PavrL.regs0 PavrL.regs_out10).
Lemma KS_avrL_10_ok : BG.kept_ok 60 PavrL.regs0 PavrL.regs_out10 KS_avrL_10 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avrL_11 : list nat := Eval vm_compute in (BG.kept_list 60 PavrL.regs0 PavrL.regs_out11).
Lemma KS_avrL_11_ok : BG.kept_ok 60 PavrL.regs0 PavrL.regs_out11 KS_avrL_11 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avrL_12 : list nat := Eval vm_compute in (BG.kept_list 60 PavrL.regs0 PavrL.regs_out12).
Lemma KS_avrL_12_ok : BG.kept_ok 60 PavrL.regs0 PavrL.regs_out12 KS_avrL_12 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avrL_13 : list nat := Eval vm_compute in (BG.kept_list 60 PavrL.regs0 PavrL.regs_out13).
Lemma KS_avrL_13_ok : BG.kept_ok 60 PavrL.regs0 PavrL.regs_out13 KS_avrL_13 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 39%nat) -> getr R (reg 12) = Z_to_bv 64 (V 34%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 23) = Z_to_bv 64 (V 36%nat) -> getr R (reg 24) = Z_to_bv 64 (V 37%nat) -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  0 <= (V 34%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb5d88 M) (st fx' R' 0xb5e90 M')
        /\ (forall x, In x KS_avrL_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ (Z.land (V 39%nat) 255) < 144
        /\ (((V 37%nat) - 240) mod 2 ^ 64) < 1
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit 239) (EVar 37))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb5d88 M) (st fx' R' 0xb5dd4 M')
        /\ (forall x, In x KS_avrL_1 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 11)) = (Z.land (V 39%nat) 255)
        /\ 144 <= (Z.land (V 39%nat) 255)
        /\ (((V 37%nat) - 240) mod 2 ^ 64) < 1
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit 239) (EVar 37))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb5d88 M) (st fx' R' 0xb5e90 M')
        /\ (forall x, In x KS_avrL_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ 143 < (Z.land (V 39%nat) 255)
        /\ (((V 37%nat) - 244) mod 2 ^ 64) < 1
        /\ 1 <= (((V 37%nat) - 240) mod 2 ^ 64)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit 239) (EVar 37))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb5d88 M) (st fx' R' 0xb5dd4 M')
        /\ (forall x, In x KS_avrL_3 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 11)) = (Z.land (V 39%nat) 255)
        /\ (Z.land (V 39%nat) 255) <= 143
        /\ (((V 37%nat) - 244) mod 2 ^ 64) < 1
        /\ 1 <= (((V 37%nat) - 240) mod 2 ^ 64)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit 239) (EVar 37))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb5d88 M) (st fx' R' 0xb5e90 M')
        /\ (forall x, In x KS_avrL_4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 13) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 36)) (ELit 56))
        /\ bv_unsigned (getr R' (reg 23)) = ((72057594037927936 * (V 36%nat)) mod 2 ^ 64)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 36)) (ELit 56)) (ELit (-62)))) <= 1
        /\ 1 <= (((V 37%nat) - 244) mod 2 ^ 64)
        /\ 1 <= (((V 37%nat) - 240) mod 2 ^ 64)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit 239) (EVar 37))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb5d88 M) (st fx' R' 0xb5dd4 M')
        /\ (forall x, In x KS_avrL_5 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 13) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 36)) (ELit 56))
        /\ bv_unsigned (getr R' (reg 23)) = ((72057594037927936 * (V 36%nat)) mod 2 ^ 64)
        /\ (V 37%nat) < 245
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 36)) (ELit 56)) (ELit (-62)))) <= 0
        /\ 1 <= (((V 37%nat) - 244) mod 2 ^ 64)
        /\ 1 <= (((V 37%nat) - 240) mod 2 ^ 64)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit 239) (EVar 37))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb5d88 M) (st fx' R' 0xb5e90 M')
        /\ (forall x, In x KS_avrL_6 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 13) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 36)) (ELit 56))
        /\ bv_unsigned (getr R' (reg 23)) = ((72057594037927936 * (V 36%nat)) mod 2 ^ 64)
        /\ 245 <= (V 37%nat)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 36)) (ELit 56)) (ELit (-62)))) <= 0
        /\ 1 <= (((V 37%nat) - 244) mod 2 ^ 64)
        /\ 1 <= (((V 37%nat) - 240) mod 2 ^ 64)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit 239) (EVar 37))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb5d88 M) (st fx' R' 0xb5e90 M')
        /\ (forall x, In x KS_avrL_7 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ (Z.land (V 39%nat) 255) < 160
        /\ (((V 37%nat) - 224) mod 2 ^ 64) < 1
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit 239) (EVar 37))) <= 0)
      \/ (msteps RSEGS (st fx R 0xb5d88 M) (st fx' R' 0xb5dd4 M')
        /\ (forall x, In x KS_avrL_8 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 11)) = (Z.land (V 39%nat) 255)
        /\ 160 <= (Z.land (V 39%nat) 255)
        /\ (((V 37%nat) - 224) mod 2 ^ 64) < 1
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit 239) (EVar 37))) <= 0)
      \/ (msteps RSEGS (st fx R 0xb5d88 M) (st fx' R' 0xb5e90 M')
        /\ (forall x, In x KS_avrL_9 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ 159 < (Z.land (V 39%nat) 255)
        /\ (((V 37%nat) - 237) mod 2 ^ 64) < 1
        /\ 1 <= (((V 37%nat) - 224) mod 2 ^ 64)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit 239) (EVar 37))) <= 0)
      \/ (msteps RSEGS (st fx R 0xb5d88 M) (st fx' R' 0xb5dd4 M')
        /\ (forall x, In x KS_avrL_10 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 11)) = (Z.land (V 39%nat) 255)
        /\ (Z.land (V 39%nat) 255) <= 159
        /\ (((V 37%nat) - 237) mod 2 ^ 64) < 1
        /\ 1 <= (((V 37%nat) - 224) mod 2 ^ 64)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit 239) (EVar 37))) <= 0)
      \/ (msteps RSEGS (st fx R 0xb5d88 M) (st fx' R' 0xb5e90 M')
        /\ (forall x, In x KS_avrL_11 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 13) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 36)) (ELit 56))
        /\ bv_unsigned (getr R' (reg 23)) = ((72057594037927936 * (V 36%nat)) mod 2 ^ 64)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 36)) (ELit 56)) (ELit (-62)))) <= 1
        /\ 1 <= (((V 37%nat) - 237) mod 2 ^ 64)
        /\ 1 <= (((V 37%nat) - 224) mod 2 ^ 64)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit 239) (EVar 37))) <= 0)
      \/ (msteps RSEGS (st fx R 0xb5d88 M) (st fx' R' 0xb5dd4 M')
        /\ (forall x, In x KS_avrL_12 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 13) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 36)) (ELit 56))
        /\ bv_unsigned (getr R' (reg 23)) = ((72057594037927936 * (V 36%nat)) mod 2 ^ 64)
        /\ (V 37%nat) < 245
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 36)) (ELit 56)) (ELit (-62)))) <= 0
        /\ 1 <= (((V 37%nat) - 237) mod 2 ^ 64)
        /\ 1 <= (((V 37%nat) - 224) mod 2 ^ 64)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit 239) (EVar 37))) <= 0)
      \/ (msteps RSEGS (st fx R 0xb5d88 M) (st fx' R' 0xb5e90 M')
        /\ (forall x, In x KS_avrL_13 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 13) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 36)) (ELit 56))
        /\ bv_unsigned (getr R' (reg 23)) = ((72057594037927936 * (V 36%nat)) mod 2 ^ 64)
        /\ 245 <= (V 37%nat)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 36)) (ELit 56)) (ELit (-62)))) <= 0
        /\ 1 <= (((V 37%nat) - 237) mod 2 ^ 64)
        /\ 1 <= (((V 37%nat) - 224) mod 2 ^ 64)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit 239) (EVar 37))) <= 0)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G5 G6 G7 G8 G9 G10 G11 G12 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G28 G29 G30 G31 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV37l; move HV37l before pvzI6; pose proof (proj2 pvzI6) as HV37r; move HV37r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV39l; move HV39l before pvzI7; pose proof (proj2 pvzI7) as HV39r; move HV39r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K1l; move K1l before pvzI9; pose proof (proj2 pvzI9) as K1r; move K1r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K2l; move K2l before pvzI10; pose proof (proj2 pvzI10) as K2r; move K2r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K3l; move K3l before pvzI11; pose proof (proj2 pvzI11) as K3r; move K3r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K4l; move K4l before pvzI12; pose proof (proj2 pvzI12) as K4r; move K4r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_39 := V 39%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 39%nat => Z_to_bv 64 vz_39 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 39%nat => vz_39 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 40%nat. }
  assert (HR: regs_ok E PavrL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrL.kn0).
  { unfold know_ok, PavrL.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrL.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavrL.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PavrL.ps0) with 0xb5e90 in Hms. change (SR.ps_regs PavrL.ps0) with (map (fun i => (i, nth i PavrL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrL.ps0) with PavrL.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrL.regs0 PavrL.regs_out0 60 KS_avrL_0 KS_avrL_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrL.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. left.
    change (SR.ps_pc PavrL.ps1) with 0xb5dd4 in Hms. change (SR.ps_regs PavrL.ps1) with (map (fun i => (i, nth i PavrL.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrL.ps1) with PavrL.cells1 in Hcells. unfold PavrL.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrL.regs0 PavrL.regs_out1 60 KS_avrL_1 KS_avrL_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrL.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrL.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. left.
    change (SR.ps_pc PavrL.ps2) with 0xb5e90 in Hms. change (SR.ps_regs PavrL.ps2) with (map (fun i => (i, nth i PavrL.regs_out2 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrL.ps2) with PavrL.cells2 in Hcells. unfold PavrL.cells2 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrL.regs0 PavrL.regs_out2 60 KS_avrL_2 KS_avrL_2_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrL.regs_out2 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrL.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. left.
    change (SR.ps_pc PavrL.ps3) with 0xb5dd4 in Hms. change (SR.ps_regs PavrL.ps3) with (map (fun i => (i, nth i PavrL.regs_out3 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrL.ps3) with PavrL.cells3 in Hcells. unfold PavrL.cells3 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrL.regs0 PavrL.regs_out3 60 KS_avrL_3 KS_avrL_3_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrL.regs_out3 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrL.regs_out3]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. left.
    change (SR.ps_pc PavrL.ps4) with 0xb5e90 in Hms. change (SR.ps_regs PavrL.ps4) with (map (fun i => (i, nth i PavrL.regs_out4 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrL.ps4) with PavrL.cells4 in Hcells. unfold PavrL.cells4 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrL.regs0 PavrL.regs_out4 60 KS_avrL_4 KS_avrL_4_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrL.regs_out4 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrL.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrL.regs_out4 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrL.regs_out4]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    split. { rewrite (BG.out_reg PavrL.regs_out4 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrL.regs_out4]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. left.
    change (SR.ps_pc PavrL.ps5) with 0xb5dd4 in Hms. change (SR.ps_regs PavrL.ps5) with (map (fun i => (i, nth i PavrL.regs_out5 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrL.ps5) with PavrL.cells5 in Hcells. unfold PavrL.cells5 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrL.regs0 PavrL.regs_out5 60 KS_avrL_5 KS_avrL_5_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrL.regs_out5 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrL.regs_out5]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrL.regs_out5 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrL.regs_out5]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    split. { rewrite (BG.out_reg PavrL.regs_out5 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrL.regs_out5]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. left.
    change (SR.ps_pc PavrL.ps6) with 0xb5e90 in Hms. change (SR.ps_regs PavrL.ps6) with (map (fun i => (i, nth i PavrL.regs_out6 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrL.ps6) with PavrL.cells6 in Hcells. unfold PavrL.cells6 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrL.regs0 PavrL.regs_out6 60 KS_avrL_6 KS_avrL_6_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrL.regs_out6 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrL.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrL.regs_out6 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrL.regs_out6]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    split. { rewrite (BG.out_reg PavrL.regs_out6 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrL.regs_out6]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. left.
    change (SR.ps_pc PavrL.ps7) with 0xb5e90 in Hms. change (SR.ps_regs PavrL.ps7) with (map (fun i => (i, nth i PavrL.regs_out7 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrL.ps7) with PavrL.cells7 in Hcells. unfold PavrL.cells7 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrL.regs0 PavrL.regs_out7 60 KS_avrL_7 KS_avrL_7_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrL.regs_out7 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrL.regs_out7]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. right. left.
    change (SR.ps_pc PavrL.ps8) with 0xb5dd4 in Hms. change (SR.ps_regs PavrL.ps8) with (map (fun i => (i, nth i PavrL.regs_out8 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrL.ps8) with PavrL.cells8 in Hcells. unfold PavrL.cells8 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrL.regs0 PavrL.regs_out8 60 KS_avrL_8 KS_avrL_8_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrL.regs_out8 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrL.regs_out8]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. right. right. left.
    change (SR.ps_pc PavrL.ps9) with 0xb5e90 in Hms. change (SR.ps_regs PavrL.ps9) with (map (fun i => (i, nth i PavrL.regs_out9 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrL.ps9) with PavrL.cells9 in Hcells. unfold PavrL.cells9 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrL.regs0 PavrL.regs_out9 60 KS_avrL_9 KS_avrL_9_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrL.regs_out9 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrL.regs_out9]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. right. right. right. left.
    change (SR.ps_pc PavrL.ps10) with 0xb5dd4 in Hms. change (SR.ps_regs PavrL.ps10) with (map (fun i => (i, nth i PavrL.regs_out10 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrL.ps10) with PavrL.cells10 in Hcells. unfold PavrL.cells10 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrL.regs0 PavrL.regs_out10 60 KS_avrL_10 KS_avrL_10_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrL.regs_out10 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrL.regs_out10]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. right. right. right. right. left.
    change (SR.ps_pc PavrL.ps11) with 0xb5e90 in Hms. change (SR.ps_regs PavrL.ps11) with (map (fun i => (i, nth i PavrL.regs_out11 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrL.ps11) with PavrL.cells11 in Hcells. unfold PavrL.cells11 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrL.regs0 PavrL.regs_out11 60 KS_avrL_11 KS_avrL_11_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrL.regs_out11 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrL.regs_out11]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrL.regs_out11 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrL.regs_out11]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    split. { rewrite (BG.out_reg PavrL.regs_out11 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrL.regs_out11]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. right. right. right. right. right. left.
    change (SR.ps_pc PavrL.ps12) with 0xb5dd4 in Hms. change (SR.ps_regs PavrL.ps12) with (map (fun i => (i, nth i PavrL.regs_out12 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrL.ps12) with PavrL.cells12 in Hcells. unfold PavrL.cells12 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrL.regs0 PavrL.regs_out12 60 KS_avrL_12 KS_avrL_12_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrL.regs_out12 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrL.regs_out12]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrL.regs_out12 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrL.regs_out12]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    split. { rewrite (BG.out_reg PavrL.regs_out12 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrL.regs_out12]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right. right. right. right. right. right. right.
    change (SR.ps_pc PavrL.ps13) with 0xb5e90 in Hms. change (SR.ps_regs PavrL.ps13) with (map (fun i => (i, nth i PavrL.regs_out13 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrL.ps13) with PavrL.cells13 in Hcells. unfold PavrL.cells13 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrL.regs0 PavrL.regs_out13 60 KS_avrL_13 KS_avrL_13_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrL.regs_out13 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrL.regs_out13]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrL.regs_out13 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrL.regs_out13]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    split. { rewrite (BG.out_reg PavrL.regs_out13 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrL.regs_out13]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.

Module PavrB := BndP_Ea_060S8.LibSegEa_avrB.
Definition KS_avrB_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrB.regs0 PavrB.regs_out0).
Lemma KS_avrB_0_ok : BG.kept_ok 60 PavrB.regs0 PavrB.regs_out0 KS_avrB_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avrB_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrB.regs0 PavrB.regs_out1).
Lemma KS_avrB_1_ok : BG.kept_ok 60 PavrB.regs0 PavrB.regs_out1 KS_avrB_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 0 <= (V 35%nat) <= 140737488355328 -> 0 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb5dd4 M) (st fx' R' 0xb5e90 M')
        /\ (forall x, In x KS_avrB_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + (V 35%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ (((V 33%nat) - (((V 33%nat) + (V 35%nat)) mod 2 ^ 64)) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0xb5dd4 M) (st fx' R' 0xb5bec M')
        /\ (forall x, In x KS_avrB_1 -> getr R' (reg x) = getr R (reg x))
        /\ 1 <= (((V 33%nat) - (((V 33%nat) + (V 35%nat)) mod 2 ^ 64)) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G5 G6 G7 G8 G9 G12 G14 G15 G16 G17 G18 G19 G20 G21 G22 G28 G29 G30 G31 pvzI4 pvzI5 pvzI6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K1l; move K1l before pvzI5; pose proof (proj2 pvzI5) as K1r; move K1r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K2l; move K2l before pvzI6; pose proof (proj2 pvzI6) as K2r; move K2r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 36%nat. }
  assert (HR: regs_ok E PavrB.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrB.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrB.kn0).
  { unfold know_ok, PavrB.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrB.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrB.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavrB.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavrB.ps0) with 0xb5e90 in Hms. change (SR.ps_regs PavrB.ps0) with (map (fun i => (i, nth i PavrB.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrB.ps0) with PavrB.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrB.regs0 PavrB.regs_out0 60 KS_avrB_0 KS_avrB_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrB.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrB.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  - right.
    change (SR.ps_pc PavrB.ps1) with 0xb5bec in Hms. change (SR.ps_regs PavrB.ps1) with (map (fun i => (i, nth i PavrB.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrB.ps1) with PavrB.cells1 in Hcells. unfold PavrB.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrB.regs0 PavrB.regs_out1 60 KS_avrB_1 KS_avrB_1_ok HR Hag Hregs j Hj). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
Qed.

Module PavrX := BndP_Ea_067S8.LibSegEa_avrX.
Definition KS_avrX : list nat := Eval vm_compute in (BG.kept_list 60 PavrX.regs0 PavrX.regs_out0).
Lemma KS_avrX_ok : BG.kept_ok 60 PavrX.regs0 PavrX.regs_out0 KS_avrX = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrX_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) ->
  140735332487264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 41%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 51%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5e90 M) (st fx' R' 0xb5ec4 M')
        /\ (forall x, In x KS_avrX -> getr R' (reg x) = getr R (reg x))
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
        /\ getr R' (reg 26) = Z_to_bv 64 (V 51%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 G2 pvzI14 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV40l; move HV40l before pvzI2; pose proof (proj2 pvzI2) as HV40r; move HV40r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV41l; move HV41l before pvzI3; pose proof (proj2 pvzI3) as HV41r; move HV41r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV42l; move HV42l before pvzI4; pose proof (proj2 pvzI4) as HV42r; move HV42r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV43l; move HV43l before pvzI5; pose proof (proj2 pvzI5) as HV43r; move HV43r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV44l; move HV44l before pvzI6; pose proof (proj2 pvzI6) as HV44r; move HV44r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV45l; move HV45l before pvzI7; pose proof (proj2 pvzI7) as HV45r; move HV45r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV46l; move HV46l before pvzI8; pose proof (proj2 pvzI8) as HV46r; move HV46r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV47l; move HV47l before pvzI9; pose proof (proj2 pvzI9) as HV47r; move HV47r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV48l; move HV48l before pvzI10; pose proof (proj2 pvzI10) as HV48r; move HV48r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV49l; move HV49l before pvzI11; pose proof (proj2 pvzI11) as HV49r; move HV49r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV50l; move HV50l before pvzI12; pose proof (proj2 pvzI12) as HV50r; move HV50r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV51l; move HV51l before pvzI13; pose proof (proj2 pvzI13) as HV51r; move HV51r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K0l; move K0l before pvzI14; pose proof (proj2 pvzI14) as K0r; move K0r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 40%nat => vz_40 | 41%nat => vz_41 | 42%nat => vz_42 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PavrX.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrX.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrX.kn0).
  { unfold know_ok, PavrX.kn0.
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
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrX.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrX.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavrX.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PavrX.ps0) with 0xb5ec4 in Hms. change (SR.ps_regs PavrX.ps0) with (map (fun i => (i, nth i PavrX.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PavrX.ps0) with PavrX.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrX.regs0 PavrX.regs_out0 60 KS_avrX KS_avrX_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PavrX.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PavrX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavrX.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PavrX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavrX.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PavrX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavrX.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PavrX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavrX.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PavrX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavrX.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PavrX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavrX.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PavrX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavrX.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PavrX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavrX.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PavrX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavrX.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavrX.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PavrX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavrX.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PavrX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PavrX.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PavrX.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

End PECVALARP1.
