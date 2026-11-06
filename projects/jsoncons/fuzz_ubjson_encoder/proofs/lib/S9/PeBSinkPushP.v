(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BigLinkZA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Eb0PlanKit AsanPlanCore
     BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.seg Require BndP_Eb_048S9 BndP_Eb_049S9 BndP_Eb_050S9.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEBSKPP.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).

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

Module PbskA := BndP_Eb_048S9.LibSegEb_bskA.
Definition KS_bskA : list nat := Eval vm_compute in (BG.kept_list 60 PbskA.regs0 PbskA.regs_out0).
Lemma KS_bskA_ok : BG.kept_ok 60 PbskA.regs0 PbskA.regs_out0 KS_bskA = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma bskA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 -> 6930432 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> (2147446784 + 17592186048512 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= 2147446784) -> L5KA.zeros_at M (((bv_unsigned (getr R (reg 10))) / 8) + 2147450880) 3 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 ->
  (((V 2%nat) - 256) + 256 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= ((V 2%nat) - 256)) -> 4096 <= (bv_unsigned (getr R (reg 11))) <= 140737488355327 -> (2147446784 + 17592186048512 <= (bv_unsigned (getr R (reg 11))) \/ (bv_unsigned (getr R (reg 11))) + 1 <= 2147446784) -> L5KA.zeros_at M (((bv_unsigned (getr R (reg 11))) / 8) + 2147450880) 1 ->
  L5.u8_at RSEGS M (bv_unsigned (getr R (reg 11))) (V 40%nat) -> 0 <= (V 40%nat) <= 255 -> ((bv_unsigned (getr R (reg 11))) + 1 <= ((V 2%nat) - 256) \/ ((V 2%nat) - 256) + 256 <= (bv_unsigned (getr R (reg 11)))) -> ((bv_unsigned (getr R (reg 11))) + 1 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= (bv_unsigned (getr R (reg 11)))) ->
  L5.u64_at RSEGS M (bv_unsigned (getr R (reg 10))) (V 33%nat) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) ((V 33%nat) + (V 34%nat)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 16) ((V 33%nat) + (V 35%nat)) -> 4096 <= (V 33%nat) <= 140737488355328 ->
  aligned (V 33%nat) 16 -> 0 <= (V 34%nat) <= 17179869184 -> 0 <= (V 35%nat) <= 17179869184 -> 4096 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + (V 35%nat) <= 2147446784) -> (65536 + 6864896 <= (V 33%nat) \/ (V 33%nat) + (V 35%nat) <= 65536) -> 1 <= ((V 35%nat) - (V 34%nat)) <= 17179869184 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 80) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 80) <= i < ((V 2%nat) - 80) + 80) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb120c M) (st fx' R' 0xb1610 M')
        /\ (forall x, In x KS_bskA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 725784
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 8) = getr R (reg 11)
        /\ getr R' (reg 9) = Z_to_bv 64 2147450880
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + (V 34%nat))
        /\ getr R' (reg 13) = Z_to_bv 64 1
        /\ getr R' (reg 14) = Z_to_bv 64 (((bv_unsigned (getr R (reg 10))) + 16) / 8)
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 33%nat) + (V 34%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (((V 33%nat) + (V 34%nat)) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) ((V 33%nat) + (V 34%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (bv_unsigned (getr R (reg 10)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) ((((bv_unsigned (getr R (reg 10))) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) ((bv_unsigned (getr R (reg 10))) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) 725604
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 K0 K1 K2 pvzI6 K4 K5 K6 pvzI7 K8 K9 K10 K11 K12 pvzI8 K14 K15 K16 pvzI9 K18 K19 K20 K21 K22 pvzI10 K24 pvzI11 pvzI12 pvzI13 K28 K29 pvzI14.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV40l; move HV40l before pvzI5; pose proof (proj2 pvzI5) as HV40r; move HV40r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K7l; move K7l before pvzI7; pose proof (proj2 pvzI7) as K7r; move K7r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K13l; move K13l before pvzI8; pose proof (proj2 pvzI8) as K13r; move K13r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K17l; move K17l before pvzI9; pose proof (proj2 pvzI9) as K17r; move K17r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K23l; move K23l before pvzI10; pose proof (proj2 pvzI10) as K23r; move K23r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K25l; move K25l before pvzI11; pose proof (proj2 pvzI11) as K25r; move K25r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K26l; move K26l before pvzI12; pose proof (proj2 pvzI12) as K26r; move K26r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K27l; move K27l before pvzI13; pose proof (proj2 pvzI13) as K27r; move K27r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K30l; move K30l before pvzI14; pose proof (proj2 pvzI14) as K30r; move K30r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_40 := V 40%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 40%nat => Z_to_bv 64 vz_40 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 40%nat => vz_40 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 41%nat. }
  assert (HR: regs_ok E PbskA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbskA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbskA.kn0).
  { unfold know_ok, PbskA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18; lia | clear - HV2l HV2r K3l K3r K12 K18; lia | clear - HV2l HV2r K3l K3r K12 K18; lia | exactA K5]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18; lia | clear - HV2l HV2r K3l K3r K12 K18; lia | clear - HV2l HV2r K3l K3r K12 K18; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | evalEk ZA ltac:(clear) | clear - K7l K7r K9 K12 K19; lia | clear - K7l K7r K9 K12 K19; lia | clear - K7l K7r K9 K12 K19; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | evalEk ZA ltac:(clear) | clear - K7l K7r K9 K12 K19; lia | clear - K7l K7r K9 K12 K19; lia | clear - K7l K7r K9 K12 K19; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K13l K13r K14 K18 K19) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K13l K13r K14 K18 K19) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - K13l K13r K14 K18 K19) | evalEk ZA ltac:(clear) | clear - K13l K13r K14 K18 K19; lia | clear - K13l K13r K14 K18 K19; lia | clear - K13l K13r K14 K18 K19; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - K13l K13r K14 K18 K19) | evalEk ZA ltac:(clear - HV40l HV40r K17l K17r) | clear - K13l K13r K14 K18 K19; lia | clear - K13l K13r K14 K18 K19; lia | byte_tac ltac:(clear - HV40l HV40r K17l K17r) | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - K13l K13r K14 K18 K19) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - K13l K13r K14 K18 K19) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | evalEk ZA ltac:(clear - HV33l HV33r K23l K23r K27l K27r K28 K29) | clear - K7l K7r K9 K12 K19; lia | clear - K7l K7r K9 K12 K19; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | evalEk ZA ltac:(clear - HV33l HV33r K23l K23r K27l K27r K28 K29 HV34l HV34r K25l K25r K30l K30r) | clear - K7l K7r K9 K12 K19; lia | clear - K7l K7r K9 K12 K19; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | evalEk ZA ltac:(clear - HV33l HV33r K23l K23r K27l K27r K28 K29 HV35l HV35r K26l K26r K30l K30r) | clear - K7l K7r K9 K12 K19; lia | clear - K7l K7r K9 K12 K19; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K23l K23r K27l K27r K28 K29) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K23l K23r K27l K27r K28 K29) | clear; lia | exact K24]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K25l K25r K30l K30r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K26l K26r K27l K27r K28 K29 K30l K30r) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K23l K23r K27l K27r K28 K29 HV35l HV35r K26l K26r K30l K30r) | exact (conj K27l K27r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K23l K23r K27l K27r K28 K29) | evalEk ZA ltac:(clear - HV35l HV35r K26l K26r K27l K27r K28 K29 K30l K30r) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K23l K23r K27l K27r K28 K29) | evalEk ZA ltac:(clear - HV35l HV35r K26l K26r K27l K27r K28 K29 K30l K30r) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K25l K25r K30l K30r HV35l HV35r K26l K26r K27l K27r K28 K29) | exact (conj K30l K30r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbskA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbskA.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 80) <= bv_unsigned a < (vz_2 - 80) + 80) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbskA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbskA.ps0) with 0xb1610 in Hms. change (SR.ps_regs PbskA.ps0) with (map (fun i => (i, nth i PbskA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbskA.ps0) with PbskA.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbskA.regs0 PbskA.regs_out0 60 KS_bskA KS_bskA_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbskA.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbskA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskA.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbskA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskA.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbskA.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PbskA.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbskA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskA.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbskA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskA.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbskA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskA.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbskA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskA.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbskA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskA.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbskA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K23l K23r K27l K27r K28 K29 HV34l HV34r K25l K25r K30l K30r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K23l K23r K27l K27r K28 K29 HV34l HV34r K25l K25r K30l K30r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - K7l K7r K9 K12 K19) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - K7l K7r K9 K12 K19) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - K7l K7r K9 K12 K19) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PbskAS := BndP_Eb_048S9.LibSegEb_bskAS.
Definition KS_bskAS : list nat := Eval vm_compute in (BG.kept_list 60 PbskAS.regs0 PbskAS.regs_out0).
Lemma KS_bskAS_ok : BG.kept_ok 60 PbskAS.regs0 PbskAS.regs_out0 KS_bskAS = true. Proof. vm_compute. reflexivity. Qed.
Lemma bskAS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 -> 6930432 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> (2147446784 + 17592186048512 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= 2147446784) -> L5KA.zeros_at M (((bv_unsigned (getr R (reg 10))) / 8) + 2147450880) 3 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 ->
  (((V 2%nat) - 256) + 256 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= ((V 2%nat) - 256)) -> 4096 <= (bv_unsigned (getr R (reg 11))) <= 140737488355327 -> (2147446784 + 17592186048512 <= (bv_unsigned (getr R (reg 11))) \/ (bv_unsigned (getr R (reg 11))) + 1 <= 2147446784) -> L5KA.zeros_at M (((bv_unsigned (getr R (reg 11))) / 8) + 2147450880) 1 ->
  L5.u8_at RSEGS M (bv_unsigned (getr R (reg 11))) (V 40%nat) -> 0 <= (V 40%nat) <= 255 -> ((bv_unsigned (getr R (reg 11))) + 1 <= ((V 2%nat) - 256) \/ ((V 2%nat) - 256) + 256 <= (bv_unsigned (getr R (reg 11)))) -> ((bv_unsigned (getr R (reg 11))) + 1 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= (bv_unsigned (getr R (reg 11)))) ->
  L5.u64_at RSEGS M (bv_unsigned (getr R (reg 10))) (V 33%nat) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) ((V 33%nat) + (V 34%nat)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 16) ((V 33%nat) + (V 34%nat)) -> 0 <= (V 33%nat) <= 140737488355328 ->
  0 <= (V 34%nat) <= 17179869184 -> 0 <= (V 35%nat) <= 17179869184 -> 0 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 32) <= bv_unsigned a < ((V 2%nat) - 32) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 32) <= i < ((V 2%nat) - 32) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb120c M) (st fx' R' 0xb13a0 M')
        /\ (forall x, In x KS_bskAS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 725624
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 32)
        /\ getr R' (reg 8) = Z_to_bv 64 ((bv_unsigned (getr R (reg 10))) + 8)
        /\ getr R' (reg 9) = Z_to_bv 64 ((((bv_unsigned (getr R (reg 10))) + 8) / 8) + 2147450880)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + (V 34%nat))
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 (((bv_unsigned (getr R (reg 10))) + 16) / 8)
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 33%nat) + (V 34%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 K0 K1 K2 pvzI6 K4 K5 K6 pvzI7 K8 K9 K10 K11 K12 pvzI8 K14 K15 K16 pvzI9 K18 K19 K20 K21 K22 pvzI10 pvzI11 pvzI12 pvzI13.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV40l; move HV40l before pvzI5; pose proof (proj2 pvzI5) as HV40r; move HV40r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K7l; move K7l before pvzI7; pose proof (proj2 pvzI7) as K7r; move K7r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K13l; move K13l before pvzI8; pose proof (proj2 pvzI8) as K13r; move K13r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K17l; move K17l before pvzI9; pose proof (proj2 pvzI9) as K17r; move K17r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K23l; move K23l before pvzI10; pose proof (proj2 pvzI10) as K23r; move K23r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K24l; move K24l before pvzI11; pose proof (proj2 pvzI11) as K24r; move K24r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K25l; move K25l before pvzI12; pose proof (proj2 pvzI12) as K25r; move K25r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K26l; move K26l before pvzI13; pose proof (proj2 pvzI13) as K26r; move K26r before pvzI13; clear pvzI13.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_40 := V 40%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 40%nat => Z_to_bv 64 vz_40 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 40%nat => vz_40 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 41%nat. }
  assert (HR: regs_ok E PbskAS.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbskAS.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbskAS.kn0).
  { unfold know_ok, PbskAS.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18; lia | clear - HV2l HV2r K3l K3r K12 K18; lia | clear - HV2l HV2r K3l K3r K12 K18; lia | exactA K5]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18; lia | clear - HV2l HV2r K3l K3r K12 K18; lia | clear - HV2l HV2r K3l K3r K12 K18; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | evalEk ZA ltac:(clear) | clear - K7l K7r K9 K12 K19; lia | clear - K7l K7r K9 K12 K19; lia | clear - K7l K7r K9 K12 K19; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | evalEk ZA ltac:(clear) | clear - K7l K7r K9 K12 K19; lia | clear - K7l K7r K9 K12 K19; lia | clear - K7l K7r K9 K12 K19; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K13l K13r K14 K18 K19) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K13l K13r K14 K18 K19) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - K13l K13r K14 K18 K19) | evalEk ZA ltac:(clear) | clear - K13l K13r K14 K18 K19; lia | clear - K13l K13r K14 K18 K19; lia | clear - K13l K13r K14 K18 K19; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - K13l K13r K14 K18 K19) | evalEk ZA ltac:(clear - HV40l HV40r K17l K17r) | clear - K13l K13r K14 K18 K19; lia | clear - K13l K13r K14 K18 K19; lia | byte_tac ltac:(clear - HV40l HV40r K17l K17r) | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - K13l K13r K14 K18 K19) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - K13l K13r K14 K18 K19) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | evalEk ZA ltac:(clear - HV33l HV33r K23l K23r K26l K26r) | clear - K7l K7r K9 K12 K19; lia | clear - K7l K7r K9 K12 K19; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | evalEk ZA ltac:(clear - HV33l HV33r K23l K23r K26l K26r HV34l HV34r K24l K24r) | clear - K7l K7r K9 K12 K19; lia | clear - K7l K7r K9 K12 K19; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | evalEk ZA ltac:(clear - HV33l HV33r K23l K23r K26l K26r HV34l HV34r K24l K24r) | clear - K7l K7r K9 K12 K19; lia | clear - K7l K7r K9 K12 K19; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K23l K23r K26l K26r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K24l K24r) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K25l K25r K26l K26r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K23l K23r K26l K26r HV35l HV35r K25l K25r) | exact (conj K26l K26r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbskAS.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbskAS.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 32) <= bv_unsigned a < (vz_2 - 32) + 32) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbskAS.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbskAS.ps0) with 0xb13a0 in Hms. change (SR.ps_regs PbskAS.ps0) with (map (fun i => (i, nth i PbskAS.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbskAS.ps0) with PbskAS.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbskAS.regs0 PbskAS.regs_out0 60 KS_bskAS KS_bskAS_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbskAS.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbskAS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskAS.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbskAS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskAS.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbskAS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskAS.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbskAS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskAS.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbskAS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskAS.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbskAS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskAS.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbskAS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskAS.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbskAS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PbskB7 := BndP_Eb_048S9.LibSegEb_bskB7.
Definition KS_bskB7 : list nat := Eval vm_compute in (BG.kept_list 60 PbskB7.regs0 PbskB7.regs_out0).
Lemma KS_bskB7_ok : BG.kept_ok 60 PbskB7.regs0 PbskB7.regs_out0 KS_bskB7 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bskB7_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 2147450880 -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + (V 34%nat)) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 -> 6930432 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 10%nat) 24 ->
  (((V 2%nat) - 256) + 256 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 256)) -> 4096 <= (V 36%nat) <= 140737488355327 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 1 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 1 ->
  L5.u8_at RSEGS M (V 36%nat) (V 40%nat) -> 0 <= (V 40%nat) <= 255 -> ((V 36%nat) + 1 <= ((V 2%nat) - 256) \/ ((V 2%nat) - 256) + 256 <= (V 36%nat)) -> ((V 36%nat) + 1 <= (V 10%nat) \/ (V 10%nat) + 24 <= (V 36%nat)) ->
  4096 <= (V 33%nat) <= 140737488355328 -> aligned (V 33%nat) 16 -> 0 <= (V 34%nat) <= 17179869184 -> 0 <= (V 35%nat) <= 17179869184 ->
  4096 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + (V 35%nat) <= 2147446784) -> (65536 + 6864896 <= (V 33%nat) \/ (V 33%nat) + (V 35%nat) <= 65536) -> L5.writable RSEGS M ((V 33%nat) + (V 34%nat)) 1 ->
  (2147446784 + 17592186048512 <= ((V 33%nat) + (V 34%nat)) \/ ((V 33%nat) + (V 34%nat)) + 1 <= 2147446784) -> (((V 33%nat) + (V 34%nat)) + 1 <= ((V 2%nat) - 256) \/ ((V 2%nat) - 256) + 256 <= ((V 33%nat) + (V 34%nat))) -> (((V 33%nat) + (V 34%nat)) + 1 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 33%nat) + (V 34%nat))) -> (((V 33%nat) + (V 34%nat)) + 1 <= (V 36%nat) \/ (V 36%nat) + 1 <= ((V 33%nat) + (V 34%nat))) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (V 10%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) ((V 33%nat) + (V 34%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (((V 33%nat) + (V 34%nat)) + 1) -> 1 <= ((V 35%nat) - (V 34%nat)) <= 17179869184 ->
  (65536 + 6864896 <= ((V 33%nat) + (V 34%nat)) \/ ((V 33%nat) + (V 34%nat)) + 1 <= 65536) -> L5.u64_at RSEGS M (V 10%nat) (V 33%nat) -> L5.u64_at RSEGS M ((V 10%nat) + 8) ((V 33%nat) + (V 34%nat)) -> L5.u64_at RSEGS M ((V 10%nat) + 16) ((V 33%nat) + (V 35%nat)) ->
  L5KA.zeros_at M ((((V 33%nat) + (V 34%nat)) / 8) + 2147450880) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((((V 33%nat) + (V 34%nat)) + 0) <= bv_unsigned a < (((V 33%nat) + (V 34%nat)) + 0) + 1) -> ~ (((V 10%nat) + 8) <= bv_unsigned a < ((V 10%nat) + 8) + 8) -> ~ (((V 2%nat) - 72) <= bv_unsigned a < ((V 2%nat) - 72) + 8) -> ~ (((V 2%nat) - 96) <= bv_unsigned a < ((V 2%nat) - 96) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((((V 33%nat) + (V 34%nat)) + 0) <= i < (((V 33%nat) + (V 34%nat)) + 0) + 1) -> ~ (((V 10%nat) + 8) <= i < ((V 10%nat) + 8) + 8) -> ~ (((V 2%nat) - 72) <= i < ((V 2%nat) - 72) + 8) -> ~ (((V 2%nat) - 96) <= i < ((V 2%nat) - 96) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1318 M) (st fx' R' 0xb15e4 M')
        /\ (forall x, In x KS_bskB7 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 725860
        /\ getr R' (reg 10) = Z_to_bv 64 (V 10%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 33%nat) + (V 34%nat)) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 (((V 33%nat) + (V 34%nat)) + 1)
        /\ getr R' (reg 14) = Z_to_bv 64 2147450880
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 10%nat) + 8) (((V 33%nat) + (V 34%nat)) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (((V 33%nat) + (V 34%nat)) + 1)
        /\ L5.u8_at RSEGS M' ((V 33%nat) + (V 34%nat)) (V 40%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 G2 G8 G9 G10 G11 G12 G18 K0 K1 K2 pvzI11 K4 K5 K6 pvzI12 K8 K9 K10 K11 K12 pvzI13 K14 K15 K16 pvzI14 K18 K19 pvzI15 K21 pvzI16 pvzI17 pvzI18 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 pvzI19 K36 K37 K38 K39 K40.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV35l; move HV35l before pvzI5; pose proof (proj2 pvzI5) as HV35r; move HV35r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV36l; move HV36l before pvzI6; pose proof (proj2 pvzI6) as HV36r; move HV36r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV40l; move HV40l before pvzI7; pose proof (proj2 pvzI7) as HV40r; move HV40r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV55l; move HV55l before pvzI8; pose proof (proj2 pvzI8) as HV55r; move HV55r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV56l; move HV56l before pvzI9; pose proof (proj2 pvzI9) as HV56r; move HV56r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV57l; move HV57l before pvzI10; pose proof (proj2 pvzI10) as HV57r; move HV57r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K3l; move K3l before pvzI11; pose proof (proj2 pvzI11) as K3r; move K3r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K7l; move K7l before pvzI12; pose proof (proj2 pvzI12) as K7r; move K7r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K13l; move K13l before pvzI13; pose proof (proj2 pvzI13) as K13r; move K13r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K17l; move K17l before pvzI14; pose proof (proj2 pvzI14) as K17r; move K17r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K20l; move K20l before pvzI15; pose proof (proj2 pvzI15) as K20r; move K20r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K22l; move K22l before pvzI16; pose proof (proj2 pvzI16) as K22r; move K22r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K23l; move K23l before pvzI17; pose proof (proj2 pvzI17) as K23r; move K23r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K24l; move K24l before pvzI18; pose proof (proj2 pvzI18) as K24r; move K24r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K35l; move K35l before pvzI19; pose proof (proj2 pvzI19) as K35r; move K35r before pvzI19; clear pvzI19.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 40%nat => Z_to_bv 64 vz_40 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 40%nat => vz_40 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbskB7.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbskB7.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbskB7.kn0).
  { unfold know_ok, PbskB7.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K29) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K29) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K29) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18 K29; lia | clear - HV2l HV2r K3l K3r K12 K18 K29; lia | clear - HV2l HV2r K3l K3r K12 K18 K29; lia | exactA K5]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K29) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18 K29; lia | clear - HV2l HV2r K3l K3r K12 K18 K29; lia | clear - HV2l HV2r K3l K3r K12 K18 K29; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K30) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K30) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K30) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K30) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K7l K7r K9 K12 K19 K30; lia | clear - HV10l HV10r K7l K7r K9 K12 K19 K30; lia | clear - HV10l HV10r K7l K7r K9 K12 K19 K30; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K30) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K7l K7r K9 K12 K19 K30; lia | clear - HV10l HV10r K7l K7r K9 K12 K19 K30; lia | clear - HV10l HV10r K7l K7r K9 K12 K19 K30; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K30) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K31) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K31) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K31) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K13l K13r K14 K18 K19 K31; lia | clear - HV36l HV36r K13l K13r K14 K18 K19 K31; lia | clear - HV36l HV36r K13l K13r K14 K18 K19 K31; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K31) | evalEk ZA ltac:(clear - HV40l HV40r K17l K17r) | clear - HV36l HV36r K13l K13r K14 K18 K19 K31; lia | clear - HV36l HV36r K13l K13r K14 K18 K19 K31; lia | byte_tac ltac:(clear - HV40l HV40r K17l K17r) | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K31) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K29) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K31) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K30) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36) | clear; lia | exact K21]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K22l K22r K28 K29 K30 K31 K35l K35r K36) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K23l K23r K24l K24r K25 K26 K35l K35r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36 HV35l HV35r K23l K23r K35l K35r) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36) | evalEk ZA ltac:(clear - HV35l HV35r K23l K23r K24l K24r K25 K26 K35l K35r) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36) | evalEk ZA ltac:(clear - HV35l HV35r K23l K23r K24l K24r K25 K26 K35l K35r) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36 HV34l HV34r K22l K22r K35l K35r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36 HV34l HV34r K22l K22r K35l K35r; lia | clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36 HV34l HV34r K22l K22r K35l K35r; lia | clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36 HV34l HV34r K22l K22r K35l K35r; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36 HV34l HV34r K22l K22r K35l K35r) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36 HV34l HV34r K22l K22r K35l K35r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K29) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36 HV34l HV34r K22l K22r K35l K35r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K30) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36 HV34l HV34r K22l K22r K35l K35r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K31) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K29) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K30) | clear - HV2l HV2r K3l K3r K12 K18 K29; lia | clear - HV2l HV2r K3l K3r K12 K18 K29; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K29) | evalEk ZA ltac:(clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36 HV34l HV34r K22l K22r K35l K35r) | clear - HV2l HV2r K3l K3r K12 K18 K29; lia | clear - HV2l HV2r K3l K3r K12 K18 K29; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K29) | evalEk ZA ltac:(clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36 HV34l HV34r K22l K22r K35l K35r) | clear - HV2l HV2r K3l K3r K12 K18 K29; lia | clear - HV2l HV2r K3l K3r K12 K18 K29; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K22l K22r K28 K29 K30 K31 K35l K35r K36 HV35l HV35r K23l K23r K24l K24r K25 K26) | exact (conj K35l K35r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36 HV34l HV34r K22l K22r K35l K35r) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K30) | evalEk ZA ltac:(clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36) | clear - HV10l HV10r K7l K7r K9 K12 K19 K30; lia | clear - HV10l HV10r K7l K7r K9 K12 K19 K30; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K30) | evalEk ZA ltac:(clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36 HV34l HV34r K22l K22r K35l K35r) | clear - HV10l HV10r K7l K7r K9 K12 K19 K30; lia | clear - HV10l HV10r K7l K7r K9 K12 K19 K30; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K30) | evalEk ZA ltac:(clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36 HV35l HV35r K23l K23r K35l K35r) | clear - HV10l HV10r K7l K7r K9 K12 K19 K30; lia | clear - HV10l HV10r K7l K7r K9 K12 K19 K30; lia | exactA K39]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36 HV34l HV34r K22l K22r K35l K35r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36 HV34l HV34r K22l K22r K35l K35r; lia | clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36 HV34l HV34r K22l K22r K35l K35r; lia | clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36 HV34l HV34r K22l K22r K35l K35r; lia | exactA K40]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbskB7.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbskB7.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((vz_33 + vz_34) + 0) <= bv_unsigned a < ((vz_33 + vz_34) + 0) + 1) -> ~ ((vz_10 + 8) <= bv_unsigned a < (vz_10 + 8) + 8) -> ~ ((vz_2 - 72) <= bv_unsigned a < (vz_2 - 72) + 8) -> ~ ((vz_2 - 96) <= bv_unsigned a < (vz_2 - 96) + 16) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PbskB7.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36 HV34l HV34r K22l K22r K35l K35r) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36 HV34l HV34r K22l K22r K35l K35r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K30) | evalEk' ZA Hag ltac:(clear) | clear - HV10l HV10r K7l K7r K9 K12 K19 K30 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K29) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18 K29 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K29) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18 K29 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbskB7.ps0) with 0xb15e4 in Hms. change (SR.ps_regs PbskB7.ps0) with (map (fun i => (i, nth i PbskB7.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbskB7.ps0) with PbskB7.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbskB7.regs0 PbskB7.regs_out0 60 KS_bskB7 KS_bskB7_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbskB7.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbskB7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskB7.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbskB7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskB7.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbskB7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskB7.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbskB7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskB7.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbskB7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskB7.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbskB7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskB7.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbskB7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K30) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36 HV34l HV34r K22l K22r K35l K35r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K29) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36 HV34l HV34r K22l K22r K35l K35r) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36 HV34l HV34r K22l K22r K35l K35r) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K17l K17r) | byte_tac ltac:(clear - HV40l HV40r K17l K17r) | clear; lia].
Qed.

Module PbskBp := BndP_Eb_048S9.LibSegEb_bskBp.
Definition KS_bskBp : list nat := Eval vm_compute in (BG.kept_list 60 PbskBp.regs0 PbskBp.regs_out0).
Lemma KS_bskBp_ok : BG.kept_ok 60 PbskBp.regs0 PbskBp.regs_out0 KS_bskBp = true. Proof. vm_compute. reflexivity. Qed.
Lemma bskBp_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 2147450880 -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + (V 34%nat)) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 -> 6930432 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 10%nat) 24 ->
  (((V 2%nat) - 256) + 256 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 256)) -> 4096 <= (V 36%nat) <= 140737488355327 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 1 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 1 ->
  L5.u8_at RSEGS M (V 36%nat) (V 40%nat) -> 0 <= (V 40%nat) <= 255 -> ((V 36%nat) + 1 <= ((V 2%nat) - 256) \/ ((V 2%nat) - 256) + 256 <= (V 36%nat)) -> ((V 36%nat) + 1 <= (V 10%nat) \/ (V 10%nat) + 24 <= (V 36%nat)) ->
  4096 <= (V 33%nat) <= 140737488355328 -> aligned (V 33%nat) 16 -> 0 <= (V 34%nat) <= 17179869184 -> 0 <= (V 35%nat) <= 17179869184 ->
  4096 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + (V 35%nat) <= 2147446784) -> (65536 + 6864896 <= (V 33%nat) \/ (V 33%nat) + (V 35%nat) <= 65536) -> L5.writable RSEGS M ((V 33%nat) + (V 34%nat)) 1 ->
  (2147446784 + 17592186048512 <= ((V 33%nat) + (V 34%nat)) \/ ((V 33%nat) + (V 34%nat)) + 1 <= 2147446784) -> (((V 33%nat) + (V 34%nat)) + 1 <= ((V 2%nat) - 256) \/ ((V 2%nat) - 256) + 256 <= ((V 33%nat) + (V 34%nat))) -> (((V 33%nat) + (V 34%nat)) + 1 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 33%nat) + (V 34%nat))) -> (((V 33%nat) + (V 34%nat)) + 1 <= (V 36%nat) \/ (V 36%nat) + 1 <= ((V 33%nat) + (V 34%nat))) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (V 10%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) ((V 33%nat) + (V 34%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (((V 33%nat) + (V 34%nat)) + 1) -> 1 <= ((V 35%nat) - (V 34%nat)) <= 17179869184 ->
  (65536 + 6864896 <= ((V 33%nat) + (V 34%nat)) \/ ((V 33%nat) + (V 34%nat)) + 1 <= 65536) -> L5.u64_at RSEGS M (V 10%nat) (V 33%nat) -> L5.u64_at RSEGS M ((V 10%nat) + 8) ((V 33%nat) + (V 34%nat)) -> L5.u64_at RSEGS M ((V 10%nat) + 16) ((V 33%nat) + (V 35%nat)) ->
  L5.u8_at RSEGS M ((((V 33%nat) + (V 34%nat)) / 8) + 2147450880) (((Z.land (V 34%nat) 7) + 1) mod 2 ^ 64) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((((V 33%nat) + (V 34%nat)) + 0) <= bv_unsigned a < (((V 33%nat) + (V 34%nat)) + 0) + 1) -> ~ (((V 10%nat) + 8) <= bv_unsigned a < ((V 10%nat) + 8) + 8) -> ~ (((V 2%nat) - 72) <= bv_unsigned a < ((V 2%nat) - 72) + 8) -> ~ (((V 2%nat) - 96) <= bv_unsigned a < ((V 2%nat) - 96) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((((V 33%nat) + (V 34%nat)) + 0) <= i < (((V 33%nat) + (V 34%nat)) + 0) + 1) -> ~ (((V 10%nat) + 8) <= i < ((V 10%nat) + 8) + 8) -> ~ (((V 2%nat) - 72) <= i < ((V 2%nat) - 72) + 8) -> ~ (((V 2%nat) - 96) <= i < ((V 2%nat) - 96) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1318 M) (st fx' R' 0xb15e4 M')
        /\ (forall x, In x KS_bskBp -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 725860
        /\ getr R' (reg 10) = Z_to_bv 64 (V 10%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 33%nat) + (V 34%nat)) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 (((V 33%nat) + (V 34%nat)) + 1)
        /\ getr R' (reg 14) = Z_to_bv 64 2147450880
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 10%nat) + 8) (((V 33%nat) + (V 34%nat)) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (((V 33%nat) + (V 34%nat)) + 1)
        /\ L5.u8_at RSEGS M' ((V 33%nat) + (V 34%nat)) (V 40%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 G2 G8 G9 G10 G11 G12 G18 K0 K1 K2 pvzI11 K4 K5 K6 pvzI12 K8 K9 K10 K11 K12 pvzI13 K14 K15 K16 pvzI14 K18 K19 pvzI15 K21 pvzI16 pvzI17 pvzI18 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 pvzI19 K36 K37 K38 K39 K40.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV35l; move HV35l before pvzI5; pose proof (proj2 pvzI5) as HV35r; move HV35r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV36l; move HV36l before pvzI6; pose proof (proj2 pvzI6) as HV36r; move HV36r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV40l; move HV40l before pvzI7; pose proof (proj2 pvzI7) as HV40r; move HV40r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV55l; move HV55l before pvzI8; pose proof (proj2 pvzI8) as HV55r; move HV55r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV56l; move HV56l before pvzI9; pose proof (proj2 pvzI9) as HV56r; move HV56r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV57l; move HV57l before pvzI10; pose proof (proj2 pvzI10) as HV57r; move HV57r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K3l; move K3l before pvzI11; pose proof (proj2 pvzI11) as K3r; move K3r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K7l; move K7l before pvzI12; pose proof (proj2 pvzI12) as K7r; move K7r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K13l; move K13l before pvzI13; pose proof (proj2 pvzI13) as K13r; move K13r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K17l; move K17l before pvzI14; pose proof (proj2 pvzI14) as K17r; move K17r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K20l; move K20l before pvzI15; pose proof (proj2 pvzI15) as K20r; move K20r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K22l; move K22l before pvzI16; pose proof (proj2 pvzI16) as K22r; move K22r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K23l; move K23l before pvzI17; pose proof (proj2 pvzI17) as K23r; move K23r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K24l; move K24l before pvzI18; pose proof (proj2 pvzI18) as K24r; move K24r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K35l; move K35l before pvzI19; pose proof (proj2 pvzI19) as K35r; move K35r before pvzI19; clear pvzI19.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 40%nat => Z_to_bv 64 vz_40 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 40%nat => vz_40 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbskBp.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbskBp.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbskBp.kn0).
  { unfold know_ok, PbskBp.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K29) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K29) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K29) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18 K29; lia | clear - HV2l HV2r K3l K3r K12 K18 K29; lia | clear - HV2l HV2r K3l K3r K12 K18 K29; lia | exactA K5]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K29) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18 K29; lia | clear - HV2l HV2r K3l K3r K12 K18 K29; lia | clear - HV2l HV2r K3l K3r K12 K18 K29; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K30) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K30) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K30) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K30) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K7l K7r K9 K12 K19 K30; lia | clear - HV10l HV10r K7l K7r K9 K12 K19 K30; lia | clear - HV10l HV10r K7l K7r K9 K12 K19 K30; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K30) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K7l K7r K9 K12 K19 K30; lia | clear - HV10l HV10r K7l K7r K9 K12 K19 K30; lia | clear - HV10l HV10r K7l K7r K9 K12 K19 K30; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K30) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K31) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K31) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K31) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K13l K13r K14 K18 K19 K31; lia | clear - HV36l HV36r K13l K13r K14 K18 K19 K31; lia | clear - HV36l HV36r K13l K13r K14 K18 K19 K31; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K31) | evalEk ZA ltac:(clear - HV40l HV40r K17l K17r) | clear - HV36l HV36r K13l K13r K14 K18 K19 K31; lia | clear - HV36l HV36r K13l K13r K14 K18 K19 K31; lia | byte_tac ltac:(clear - HV40l HV40r K17l K17r) | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K31) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K29) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K31) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K30) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36) | clear; lia | exact K21]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K22l K22r K28 K29 K30 K31 K35l K35r K36) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K23l K23r K24l K24r K25 K26 K35l K35r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36 HV35l HV35r K23l K23r K35l K35r) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36) | evalEk ZA ltac:(clear - HV35l HV35r K23l K23r K24l K24r K25 K26 K35l K35r) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36) | evalEk ZA ltac:(clear - HV35l HV35r K23l K23r K24l K24r K25 K26 K35l K35r) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36 HV34l HV34r K22l K22r K35l K35r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36 HV34l HV34r K22l K22r K35l K35r; lia | clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36 HV34l HV34r K22l K22r K35l K35r; lia | clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36 HV34l HV34r K22l K22r K35l K35r; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36 HV34l HV34r K22l K22r K35l K35r) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36 HV34l HV34r K22l K22r K35l K35r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K29) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36 HV34l HV34r K22l K22r K35l K35r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K30) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36 HV34l HV34r K22l K22r K35l K35r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K31) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K29) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K30) | clear - HV2l HV2r K3l K3r K12 K18 K29; lia | clear - HV2l HV2r K3l K3r K12 K18 K29; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K29) | evalEk ZA ltac:(clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36 HV34l HV34r K22l K22r K35l K35r) | clear - HV2l HV2r K3l K3r K12 K18 K29; lia | clear - HV2l HV2r K3l K3r K12 K18 K29; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K29) | evalEk ZA ltac:(clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36 HV34l HV34r K22l K22r K35l K35r) | clear - HV2l HV2r K3l K3r K12 K18 K29; lia | clear - HV2l HV2r K3l K3r K12 K18 K29; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K22l K22r K28 K29 K30 K31 K35l K35r K36 HV35l HV35r K23l K23r K24l K24r K25 K26) | exact (conj K35l K35r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36 HV34l HV34r K22l K22r K35l K35r) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K30) | evalEk ZA ltac:(clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36) | clear - HV10l HV10r K7l K7r K9 K12 K19 K30; lia | clear - HV10l HV10r K7l K7r K9 K12 K19 K30; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K30) | evalEk ZA ltac:(clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36 HV34l HV34r K22l K22r K35l K35r) | clear - HV10l HV10r K7l K7r K9 K12 K19 K30; lia | clear - HV10l HV10r K7l K7r K9 K12 K19 K30; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K30) | evalEk ZA ltac:(clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36 HV35l HV35r K23l K23r K35l K35r) | clear - HV10l HV10r K7l K7r K9 K12 K19 K30; lia | clear - HV10l HV10r K7l K7r K9 K12 K19 K30; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36 HV34l HV34r K22l K22r K35l K35r) | ((L5K.evalB ZA; pvz_unfold ZA); reflexivity) | clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36 HV34l HV34r K22l K22r K35l K35r; lia | clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36 HV34l HV34r K22l K22r K35l K35r; lia | byte_tac ltac:(clear - HV34l HV34r K22l K22r K28 K29 K30 K31 K35l K35r K36) | exactA K40]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbskBp.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbskBp.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((vz_33 + vz_34) + 0) <= bv_unsigned a < ((vz_33 + vz_34) + 0) + 1) -> ~ ((vz_10 + 8) <= bv_unsigned a < (vz_10 + 8) + 8) -> ~ ((vz_2 - 72) <= bv_unsigned a < (vz_2 - 72) + 8) -> ~ ((vz_2 - 96) <= bv_unsigned a < (vz_2 - 96) + 16) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PbskBp.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36 HV34l HV34r K22l K22r K35l K35r) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36 HV34l HV34r K22l K22r K35l K35r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K30) | evalEk' ZA Hag ltac:(clear) | clear - HV10l HV10r K7l K7r K9 K12 K19 K30 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K29) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18 K29 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K29) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18 K29 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbskBp.ps0) with 0xb15e4 in Hms. change (SR.ps_regs PbskBp.ps0) with (map (fun i => (i, nth i PbskBp.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbskBp.ps0) with PbskBp.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbskBp.regs0 PbskBp.regs_out0 60 KS_bskBp KS_bskBp_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbskBp.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbskBp.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskBp.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbskBp.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskBp.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbskBp.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskBp.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbskBp.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskBp.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbskBp.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskBp.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbskBp.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskBp.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbskBp.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K30) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36 HV34l HV34r K22l K22r K35l K35r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K29) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36 HV34l HV34r K22l K22r K35l K35r) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K20l K20r K24l K24r K25 K26 K28 K29 K30 K31 K36 HV34l HV34r K22l K22r K35l K35r) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K17l K17r) | byte_tac ltac:(clear - HV40l HV40r K17l K17r) | clear; lia].
Qed.

Module PbskC := BndP_Eb_049S9.LibSegEb_bskC.
Definition KS_bskC : list nat := Eval vm_compute in (BG.kept_list 60 PbskC.regs0 PbskC.regs_out0).
Lemma KS_bskC_ok : BG.kept_ok 60 PbskC.regs0 PbskC.regs_out0 KS_bskC = true. Proof. vm_compute. reflexivity. Qed.
Lemma bskC_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 -> L5.u64_at RSEGS M ((V 2%nat) - 40) 725604 ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 46%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1364 M) (st fx' R' 0xb1374 M')
        /\ (forall x, In x KS_bskC -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 725604
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 32)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G10 G11 G12 K0 K1 K2 pvzI7 K4 K5 K6 K7 K8 K9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV45l; move HV45l before pvzI2; pose proof (proj2 pvzI2) as HV45r; move HV45r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV46l; move HV46l before pvzI3; pose proof (proj2 pvzI3) as HV46r; move HV46r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV55l; move HV55l before pvzI4; pose proof (proj2 pvzI4) as HV55r; move HV55r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV56l; move HV56l before pvzI5; pose proof (proj2 pvzI5) as HV56r; move HV56r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV57l; move HV57l before pvzI6; pose proof (proj2 pvzI6) as HV57r; move HV57r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7.
  set (vz_2 := V 2%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 45%nat => vz_45 | 46%nat => vz_46 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbskC.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbskC.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbskC.kn0).
  { unfold know_ok, PbskC.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K9]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbskC.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbskC.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbskC.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbskC.ps0) with 0xb1374 in Hms. change (SR.ps_regs PbskC.ps0) with (map (fun i => (i, nth i PbskC.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbskC.ps0) with PbskC.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbskC.regs0 PbskC.regs_out0 60 KS_bskC KS_bskC_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbskC.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbskC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskC.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbskC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskC.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbskC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbskC.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbskC.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PbskD := BndP_Eb_049S9.LibSegEb_bskD.
Definition KS_bskD : list nat := Eval vm_compute in (BG.kept_list 60 PbskD.regs0 PbskD.regs_out0).
Lemma KS_bskD_ok : BG.kept_ok 60 PbskD.regs0 PbskD.regs_out0 KS_bskD = true. Proof. vm_compute. reflexivity. Qed.
Lemma bskD_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 32) -> getr R (reg 8) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 9) = Z_to_bv 64 ((((V 10%nat) + 8) / 8) + 2147450880) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + (V 34%nat)) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487200 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 32) 32 -> 6930432 <= (V 10%nat) <= 140737488355304 -> aligned (V 10%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 10%nat) 24 -> (((V 2%nat) - 256) + 256 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 256)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) ->
  4096 <= (V 33%nat) <= 140737488355328 -> aligned (V 33%nat) 16 -> 0 <= (V 34%nat) <= 17179869184 -> 0 <= (V 35%nat) <= 17179869184 ->
  4096 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + (V 35%nat) <= 2147446784) -> (65536 + 6864896 <= (V 33%nat) \/ (V 33%nat) + (V 35%nat) <= 65536) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 10%nat) + 8) <= bv_unsigned a < ((V 10%nat) + 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 10%nat) + 8) <= i < ((V 10%nat) + 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1264 M) (st fx' R' 0xb12a0 M')
        /\ (forall x, In x KS_bskD -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 33%nat) + (V 34%nat)) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 10%nat) + 8) (((V 33%nat) + (V 34%nat)) + 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 G2 G8 G9 G10 G11 G12 G18 K0 K1 K2 pvzI13 K4 K5 pvzI14 K7 K8 K9 K10 K11 K12 K13 K14 K15 pvzI15 K17 pvzI16 pvzI17 pvzI18 K21 K22.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV35l; move HV35l before pvzI5; pose proof (proj2 pvzI5) as HV35r; move HV35r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV44l; move HV44l before pvzI6; pose proof (proj2 pvzI6) as HV44r; move HV44r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV45l; move HV45l before pvzI7; pose proof (proj2 pvzI7) as HV45r; move HV45r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV46l; move HV46l before pvzI8; pose proof (proj2 pvzI8) as HV46r; move HV46r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV47l; move HV47l before pvzI9; pose proof (proj2 pvzI9) as HV47r; move HV47r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV55l; move HV55l before pvzI10; pose proof (proj2 pvzI10) as HV55r; move HV55r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV56l; move HV56l before pvzI11; pose proof (proj2 pvzI11) as HV56r; move HV56r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV57l; move HV57l before pvzI12; pose proof (proj2 pvzI12) as HV57r; move HV57r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K3l; move K3l before pvzI13; pose proof (proj2 pvzI13) as K3r; move K3r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K6l; move K6l before pvzI14; pose proof (proj2 pvzI14) as K6r; move K6r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K16l; move K16l before pvzI15; pose proof (proj2 pvzI15) as K16r; move K16r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K18l; move K18l before pvzI16; pose proof (proj2 pvzI16) as K18r; move K18r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K19l; move K19l before pvzI17; pose proof (proj2 pvzI17) as K19r; move K19r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K20l; move K20l before pvzI18; pose proof (proj2 pvzI18) as K20r; move K20r before pvzI18; clear pvzI18.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbskD.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbskD.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbskD.kn0).
  { unfold know_ok, PbskD.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K6l K6r K8 K11; lia | clear - HV10l HV10r K6l K6r K8 K11; lia | clear - HV10l HV10r K6l K6r K8 K11; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K6l K6r K8 K11; lia | clear - HV10l HV10r K6l K6r K8 K11; lia | clear - HV10l HV10r K6l K6r K8 K11; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K16l K16r K20l K20r K21 K22) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K16l K16r K20l K20r K21 K22) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K19l K19r K20l K20r K21 K22) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K16l K16r K20l K20r K21 K22 HV35l HV35r K19l K19r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K16l K16r K20l K20r K21 K22) | evalEk ZA ltac:(clear - HV35l HV35r K19l K19r K20l K20r K21 K22) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K16l K16r K20l K20r K21 K22) | evalEk ZA ltac:(clear - HV35l HV35r K19l K19r K20l K20r K21 K22) | generalize K22; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbskD.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbskD.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_10 + 8) <= bv_unsigned a < (vz_10 + 8) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbskD.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV10l HV10r K6l K6r K8 K11) | evalEk' ZA Hag ltac:(clear) | clear - HV10l HV10r K6l K6r K8 K11 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbskD.ps0) with 0xb12a0 in Hms. change (SR.ps_regs PbskD.ps0) with (map (fun i => (i, nth i PbskD.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbskD.ps0) with PbskD.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbskD.regs0 PbskD.regs_out0 60 KS_bskD KS_bskD_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbskD.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbskD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskD.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbskD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskD.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbskD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskD.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbskD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskD.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbskD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskD.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbskD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskD.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbskD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K6l K6r K8 K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K16l K16r K20l K20r K21 K22 HV34l HV34r K18l K18r) | clear; lia].
Qed.

Module PbskR := BndP_Eb_049S9.LibSegEb_bskR.
Definition KS_bskR : list nat := Eval vm_compute in (BG.kept_list 60 PbskR.regs0 PbskR.regs_out0).
Lemma KS_bskR_ok : BG.kept_ok 60 PbskR.regs0 PbskR.regs_out0 KS_bskR = true. Proof. vm_compute. reflexivity. Qed.
Lemma bskR_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 32) -> getr R (reg 8) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 9) = Z_to_bv 64 ((((V 10%nat) + 8) / 8) + 2147450880) -> getr R (reg 10) = Z_to_bv 64 (V 41%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + (V 34%nat)) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487200 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 32) 32 -> 6930432 <= (V 10%nat) <= 140737488355304 -> aligned (V 10%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 10%nat) 24 -> (((V 2%nat) - 256) + 256 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 256)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) ->
  0 <= (V 33%nat) <= 140737488355328 -> 0 <= (V 34%nat) <= 17179869184 -> 0 <= (V 35%nat) <= 17179869184 -> 0 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 ->
  2 <= (V 41%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 10%nat) + 8) <= bv_unsigned a < ((V 10%nat) + 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 10%nat) + 8) <= i < ((V 10%nat) + 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1278 M) (st fx' R' 0xb12a0 M')
        /\ (forall x, In x KS_bskR -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 10%nat) + 8) (V 41%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 G2 G8 G9 G10 G11 G12 G18 K0 K1 K2 pvzI13 K4 K5 pvzI14 K7 K8 K9 K10 K11 K12 K13 K14 K15 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV35l; move HV35l before pvzI5; pose proof (proj2 pvzI5) as HV35r; move HV35r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV41l; move HV41l before pvzI6; pose proof (proj2 pvzI6) as HV41r; move HV41r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV44l; move HV44l before pvzI7; pose proof (proj2 pvzI7) as HV44r; move HV44r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV45l; move HV45l before pvzI8; pose proof (proj2 pvzI8) as HV45r; move HV45r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV46l; move HV46l before pvzI9; pose proof (proj2 pvzI9) as HV46r; move HV46r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV47l; move HV47l before pvzI10; pose proof (proj2 pvzI10) as HV47r; move HV47r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV56l; move HV56l before pvzI11; pose proof (proj2 pvzI11) as HV56r; move HV56r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV57l; move HV57l before pvzI12; pose proof (proj2 pvzI12) as HV57r; move HV57r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K3l; move K3l before pvzI13; pose proof (proj2 pvzI13) as K3r; move K3r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K6l; move K6l before pvzI14; pose proof (proj2 pvzI14) as K6r; move K6r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K16l; move K16l before pvzI15; pose proof (proj2 pvzI15) as K16r; move K16r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K17l; move K17l before pvzI16; pose proof (proj2 pvzI16) as K17r; move K17r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K18l; move K18l before pvzI17; pose proof (proj2 pvzI17) as K18r; move K18r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K19l; move K19l before pvzI18; pose proof (proj2 pvzI18) as K19r; move K19r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K20l; move K20l before pvzI19; pose proof (proj2 pvzI19) as K20r; move K20r before pvzI19; clear pvzI19.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 41%nat => Z_to_bv 64 vz_41 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 41%nat => vz_41 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbskR.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbskR.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbskR.kn0).
  { unfold know_ok, PbskR.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K6l K6r K8 K11; lia | clear - HV10l HV10r K6l K6r K8 K11; lia | clear - HV10l HV10r K6l K6r K8 K11; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K6l K6r K8 K11; lia | clear - HV10l HV10r K6l K6r K8 K11; lia | clear - HV10l HV10r K6l K6r K8 K11; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K16l K16r K19l K19r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K18l K18r K19l K19r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K16l K16r K19l K19r HV35l HV35r K18l K18r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbskR.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbskR.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_10 + 8) <= bv_unsigned a < (vz_10 + 8) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbskR.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV10l HV10r K6l K6r K8 K11) | evalEk' ZA Hag ltac:(clear) | clear - HV10l HV10r K6l K6r K8 K11 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbskR.ps0) with 0xb12a0 in Hms. change (SR.ps_regs PbskR.ps0) with (map (fun i => (i, nth i PbskR.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbskR.ps0) with PbskR.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbskR.regs0 PbskR.regs_out0 60 KS_bskR KS_bskR_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbskR.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbskR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskR.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbskR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskR.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbskR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskR.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbskR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskR.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbskR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskR.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbskR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K6l K6r K8 K11) | evalEk' ZA Hag ltac:(clear - HV41l HV41r K20l K20r) | clear; lia].
Qed.

Module PbskS1z := BndP_Eb_049S9.LibSegEb_bskS1z.
Definition KS_bskS1z : list nat := Eval vm_compute in (BG.kept_list 60 PbskS1z.regs0 PbskS1z.regs_out0).
Lemma KS_bskS1z_ok : BG.kept_ok 60 PbskS1z.regs0 PbskS1z.regs_out0 KS_bskS1z = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma bskS1z_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 725624 -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 32) -> getr R (reg 8) = Z_to_bv 64 ((bv_unsigned (getr R (reg 10))) + 8) -> getr R (reg 9) = Z_to_bv 64 ((((bv_unsigned (getr R (reg 10))) + 8) / 8) + 2147450880) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 0 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 -> 6930432 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> (2147446784 + 17592186048512 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= 2147446784) -> L5KA.zeros_at M (((bv_unsigned (getr R (reg 10))) / 8) + 2147450880) 3 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 ->
  (((V 2%nat) - 256) + 256 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= ((V 2%nat) - 256)) -> 4096 <= (bv_unsigned (getr R (reg 11))) <= 140737488355327 -> (2147446784 + 17592186048512 <= (bv_unsigned (getr R (reg 11))) \/ (bv_unsigned (getr R (reg 11))) + 1 <= 2147446784) -> L5KA.zeros_at M (((bv_unsigned (getr R (reg 11))) / 8) + 2147450880) 1 ->
  L5.u8_at RSEGS M (bv_unsigned (getr R (reg 11))) (V 40%nat) -> 0 <= (V 40%nat) <= 255 -> ((bv_unsigned (getr R (reg 11))) + 1 <= ((V 2%nat) - 256) \/ ((V 2%nat) - 256) + 256 <= (bv_unsigned (getr R (reg 11)))) -> ((bv_unsigned (getr R (reg 11))) + 1 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= (bv_unsigned (getr R (reg 11)))) ->
  L5.u64_at RSEGS M (bv_unsigned (getr R (reg 10))) 0 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) 0 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 16) 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 192) <= bv_unsigned a < ((V 2%nat) - 192) + 160) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 192) <= i < ((V 2%nat) - 192) + 160) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb13a0 M) (st fx' R' 0x136668 M')
        /\ (forall x, In x KS_bskS1z -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 726824
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 192)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 96)
        /\ getr R' (reg 9) = Z_to_bv 64 1
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 1335544
        /\ getr R' (reg 13) = getr R (reg 10)
        /\ getr R' (reg 14) = Z_to_bv 64 4611686018427387903
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 19) = Z_to_bv 64 0
        /\ getr R' (reg 20) = Z_to_bv 64 ((((V 2%nat) - 96) / 8) + 2147450880)
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (bv_unsigned (getr R (reg 10)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((((bv_unsigned (getr R (reg 10))) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (bv_unsigned (getr R (reg 11)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (bv_unsigned (getr R (reg 10)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) ((bv_unsigned (getr R (reg 10))) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) 726092
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) ((((bv_unsigned (getr R (reg 10))) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) ((bv_unsigned (getr R (reg 10))) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) 725624).
Proof.
  intros pvzI1 pvzI2 pvzI3 G1 G2 G8 G9 G12 G18 K0 K1 K2 pvzI4 K4 K5 K6 pvzI5 K8 K9 K10 K11 K12 pvzI6 K14 K15 K16 pvzI7 K18 K19 K20 K21 K22.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV40l; move HV40l before pvzI2; pose proof (proj2 pvzI2) as HV40r; move HV40r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV57l; move HV57l before pvzI3; pose proof (proj2 pvzI3) as HV57r; move HV57r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K3l; move K3l before pvzI4; pose proof (proj2 pvzI4) as K3r; move K3r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K7l; move K7l before pvzI5; pose proof (proj2 pvzI5) as K7r; move K7r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K13l; move K13l before pvzI6; pose proof (proj2 pvzI6) as K13r; move K13r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K17l; move K17l before pvzI7; pose proof (proj2 pvzI7) as K17r; move K17r before pvzI7; clear pvzI7.
  set (vz_2 := V 2%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 40%nat => Z_to_bv 64 vz_40 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 40%nat => vz_40 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbskS1z.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbskS1z.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbskS1z.kn0).
  { unfold know_ok, PbskS1z.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18; lia | clear - HV2l HV2r K3l K3r K12 K18; lia | clear - HV2l HV2r K3l K3r K12 K18; lia | exactA K5]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18; lia | clear - HV2l HV2r K3l K3r K12 K18; lia | clear - HV2l HV2r K3l K3r K12 K18; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | evalEk ZA ltac:(clear) | clear - K7l K7r K9 K12 K19; lia | clear - K7l K7r K9 K12 K19; lia | clear - K7l K7r K9 K12 K19; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | evalEk ZA ltac:(clear) | clear - K7l K7r K9 K12 K19; lia | clear - K7l K7r K9 K12 K19; lia | clear - K7l K7r K9 K12 K19; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K13l K13r K14 K18 K19) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K13l K13r K14 K18 K19) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - K13l K13r K14 K18 K19) | evalEk ZA ltac:(clear) | clear - K13l K13r K14 K18 K19; lia | clear - K13l K13r K14 K18 K19; lia | clear - K13l K13r K14 K18 K19; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - K13l K13r K14 K18 K19) | evalEk ZA ltac:(clear - HV40l HV40r K17l K17r) | clear - K13l K13r K14 K18 K19; lia | clear - K13l K13r K14 K18 K19; lia | byte_tac ltac:(clear - HV40l HV40r K17l K17r) | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - K13l K13r K14 K18 K19) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - K13l K13r K14 K18 K19) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | evalEk ZA ltac:(clear) | clear - K7l K7r K9 K12 K19; lia | clear - K7l K7r K9 K12 K19; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | evalEk ZA ltac:(clear) | clear - K7l K7r K9 K12 K19; lia | clear - K7l K7r K9 K12 K19; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | evalEk ZA ltac:(clear) | clear - K7l K7r K9 K12 K19; lia | clear - K7l K7r K9 K12 K19; lia | exactA K22]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbskS1z.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbskS1z.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 192) <= bv_unsigned a < (vz_2 - 192) + 160) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbskS1z.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbskS1z.ps0) with 0x136668 in Hms. change (SR.ps_regs PbskS1z.ps0) with (map (fun i => (i, nth i PbskS1z.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbskS1z.ps0) with PbskS1z.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbskS1z.regs0 PbskS1z.regs_out0 60 KS_bskS1z KS_bskS1z_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbskS1z.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbskS1z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS1z.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbskS1z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS1z.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbskS1z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS1z.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbskS1z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS1z.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbskS1z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS1z.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbskS1z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS1z.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbskS1z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS1z.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbskS1z.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PbskS1z.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbskS1z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS1z.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbskS1z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS1z.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbskS1z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS1z.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbskS1z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS1z.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbskS1z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - K7l K7r K9 K12 K19) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - K7l K7r K9 K12 K19) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - K13l K13r K14 K18 K19) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - K7l K7r K9 K12 K19) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - K7l K7r K9 K12 K19) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - K7l K7r K9 K12 K19) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - K7l K7r K9 K12 K19) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PbskS1o := BndP_Eb_049S9.LibSegEb_bskS1o.
Definition KS_bskS1o : list nat := Eval vm_compute in (BG.kept_list 60 PbskS1o.regs0 PbskS1o.regs_out0).
Lemma KS_bskS1o_ok : BG.kept_ok 60 PbskS1o.regs0 PbskS1o.regs_out0 KS_bskS1o = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma bskS1o_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 725624 -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 32) -> getr R (reg 8) = Z_to_bv 64 ((bv_unsigned (getr R (reg 10))) + 8) -> getr R (reg 9) = Z_to_bv 64 ((((bv_unsigned (getr R (reg 10))) + 8) / 8) + 2147450880) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + 1) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 -> 6930432 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> (2147446784 + 17592186048512 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= 2147446784) -> L5KA.zeros_at M (((bv_unsigned (getr R (reg 10))) / 8) + 2147450880) 3 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 ->
  (((V 2%nat) - 256) + 256 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= ((V 2%nat) - 256)) -> 4096 <= (bv_unsigned (getr R (reg 11))) <= 140737488355327 -> (2147446784 + 17592186048512 <= (bv_unsigned (getr R (reg 11))) \/ (bv_unsigned (getr R (reg 11))) + 1 <= 2147446784) -> L5KA.zeros_at M (((bv_unsigned (getr R (reg 11))) / 8) + 2147450880) 1 ->
  L5.u8_at RSEGS M (bv_unsigned (getr R (reg 11))) (V 40%nat) -> 0 <= (V 40%nat) <= 255 -> ((bv_unsigned (getr R (reg 11))) + 1 <= ((V 2%nat) - 256) \/ ((V 2%nat) - 256) + 256 <= (bv_unsigned (getr R (reg 11)))) -> ((bv_unsigned (getr R (reg 11))) + 1 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= (bv_unsigned (getr R (reg 11)))) ->
  L5.u64_at RSEGS M (bv_unsigned (getr R (reg 10))) (V 33%nat) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) ((V 33%nat) + 1) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 16) ((V 33%nat) + 1) -> 4096 <= (V 33%nat) <= 140737488355327 ->
  aligned (V 33%nat) 16 -> (65536 + 6864896 <= (V 33%nat) \/ (V 33%nat) + 1 <= 65536) -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 1 <= 2147446784) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 192) <= bv_unsigned a < ((V 2%nat) - 192) + 160) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 192) <= i < ((V 2%nat) - 192) + 160) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb13a0 M) (st fx' R' 0x136668 M')
        /\ (forall x, In x KS_bskS1o -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 726824
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 192)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 96)
        /\ getr R' (reg 9) = Z_to_bv 64 2
        /\ getr R' (reg 10) = Z_to_bv 64 2
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 1335544
        /\ getr R' (reg 13) = getr R (reg 10)
        /\ getr R' (reg 14) = Z_to_bv 64 4611686018427387903
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 19) = Z_to_bv 64 1
        /\ getr R' (reg 20) = Z_to_bv 64 ((((V 2%nat) - 96) / 8) + 2147450880)
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (bv_unsigned (getr R (reg 10)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((((bv_unsigned (getr R (reg 10))) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (bv_unsigned (getr R (reg 11)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (bv_unsigned (getr R (reg 10)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) ((bv_unsigned (getr R (reg 10))) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) 726092
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) ((V 33%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) ((((bv_unsigned (getr R (reg 10))) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) ((bv_unsigned (getr R (reg 10))) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) 725624).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G1 G2 G8 G9 G12 G18 K0 K1 K2 pvzI5 K4 K5 K6 pvzI6 K8 K9 K10 K11 K12 pvzI7 K14 K15 K16 pvzI8 K18 K19 K20 K21 K22 pvzI9 K24 K25 K26.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV40l; move HV40l before pvzI3; pose proof (proj2 pvzI3) as HV40r; move HV40r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV57l; move HV57l before pvzI4; pose proof (proj2 pvzI4) as HV57r; move HV57r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K3l; move K3l before pvzI5; pose proof (proj2 pvzI5) as K3r; move K3r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K7l; move K7l before pvzI6; pose proof (proj2 pvzI6) as K7r; move K7r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K13l; move K13l before pvzI7; pose proof (proj2 pvzI7) as K13r; move K13r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K17l; move K17l before pvzI8; pose proof (proj2 pvzI8) as K17r; move K17r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K23l; move K23l before pvzI9; pose proof (proj2 pvzI9) as K23r; move K23r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 40%nat => Z_to_bv 64 vz_40 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 40%nat => vz_40 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbskS1o.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbskS1o.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbskS1o.kn0).
  { unfold know_ok, PbskS1o.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18; lia | clear - HV2l HV2r K3l K3r K12 K18; lia | clear - HV2l HV2r K3l K3r K12 K18; lia | exactA K5]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18; lia | clear - HV2l HV2r K3l K3r K12 K18; lia | clear - HV2l HV2r K3l K3r K12 K18; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | evalEk ZA ltac:(clear) | clear - K7l K7r K9 K12 K19; lia | clear - K7l K7r K9 K12 K19; lia | clear - K7l K7r K9 K12 K19; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | evalEk ZA ltac:(clear) | clear - K7l K7r K9 K12 K19; lia | clear - K7l K7r K9 K12 K19; lia | clear - K7l K7r K9 K12 K19; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K13l K13r K14 K18 K19) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K13l K13r K14 K18 K19) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - K13l K13r K14 K18 K19) | evalEk ZA ltac:(clear) | clear - K13l K13r K14 K18 K19; lia | clear - K13l K13r K14 K18 K19; lia | clear - K13l K13r K14 K18 K19; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - K13l K13r K14 K18 K19) | evalEk ZA ltac:(clear - HV40l HV40r K17l K17r) | clear - K13l K13r K14 K18 K19; lia | clear - K13l K13r K14 K18 K19; lia | byte_tac ltac:(clear - HV40l HV40r K17l K17r) | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - K13l K13r K14 K18 K19) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - K13l K13r K14 K18 K19) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | evalEk ZA ltac:(clear - HV33l HV33r K23l K23r K25 K26) | clear - K7l K7r K9 K12 K19; lia | clear - K7l K7r K9 K12 K19; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | evalEk ZA ltac:(clear - HV33l HV33r K23l K23r K25 K26) | clear - K7l K7r K9 K12 K19; lia | clear - K7l K7r K9 K12 K19; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | evalEk ZA ltac:(clear - HV33l HV33r K23l K23r K25 K26) | clear - K7l K7r K9 K12 K19; lia | clear - K7l K7r K9 K12 K19; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K23l K23r K25 K26) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K23l K23r K25 K26) | clear; lia | exact K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K23l K23r K25 K26) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K23l K23r K25 K26) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbskS1o.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbskS1o.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 192) <= bv_unsigned a < (vz_2 - 192) + 160) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbskS1o.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbskS1o.ps0) with 0x136668 in Hms. change (SR.ps_regs PbskS1o.ps0) with (map (fun i => (i, nth i PbskS1o.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbskS1o.ps0) with PbskS1o.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbskS1o.regs0 PbskS1o.regs_out0 60 KS_bskS1o KS_bskS1o_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbskS1o.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbskS1o.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS1o.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbskS1o.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS1o.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbskS1o.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS1o.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbskS1o.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS1o.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbskS1o.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS1o.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbskS1o.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS1o.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbskS1o.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS1o.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbskS1o.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PbskS1o.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbskS1o.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS1o.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbskS1o.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS1o.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbskS1o.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS1o.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbskS1o.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS1o.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbskS1o.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - K7l K7r K9 K12 K19) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - K7l K7r K9 K12 K19) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - K13l K13r K14 K18 K19) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - K7l K7r K9 K12 K19) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - K7l K7r K9 K12 K19) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K23l K23r K25 K26) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - K7l K7r K9 K12 K19) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - K7l K7r K9 K12 K19) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PbskS1 := BndP_Eb_049S9.LibSegEb_bskS1.
Definition KS_bskS1 : list nat := Eval vm_compute in (BG.kept_list 60 PbskS1.regs0 PbskS1.regs_out0).
Lemma KS_bskS1_ok : BG.kept_ok 60 PbskS1.regs0 PbskS1.regs_out0 KS_bskS1 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma bskS1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 725624 -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 32) -> getr R (reg 8) = Z_to_bv 64 ((bv_unsigned (getr R (reg 10))) + 8) -> getr R (reg 9) = Z_to_bv 64 ((((bv_unsigned (getr R (reg 10))) + 8) / 8) + 2147450880) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 -> 6930432 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> (2147446784 + 17592186048512 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= 2147446784) -> L5KA.zeros_at M (((bv_unsigned (getr R (reg 10))) / 8) + 2147450880) 3 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 ->
  (((V 2%nat) - 256) + 256 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= ((V 2%nat) - 256)) -> 4096 <= (bv_unsigned (getr R (reg 11))) <= 140737488355327 -> (2147446784 + 17592186048512 <= (bv_unsigned (getr R (reg 11))) \/ (bv_unsigned (getr R (reg 11))) + 1 <= 2147446784) -> L5KA.zeros_at M (((bv_unsigned (getr R (reg 11))) / 8) + 2147450880) 1 ->
  L5.u8_at RSEGS M (bv_unsigned (getr R (reg 11))) (V 40%nat) -> 0 <= (V 40%nat) <= 255 -> ((bv_unsigned (getr R (reg 11))) + 1 <= ((V 2%nat) - 256) \/ ((V 2%nat) - 256) + 256 <= (bv_unsigned (getr R (reg 11)))) -> ((bv_unsigned (getr R (reg 11))) + 1 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= (bv_unsigned (getr R (reg 11)))) ->
  L5.u64_at RSEGS M (bv_unsigned (getr R (reg 10))) (V 33%nat) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) ((V 33%nat) + (V 35%nat)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 16) ((V 33%nat) + (V 35%nat)) -> 4096 <= (V 33%nat) <= 140737488355328 ->
  aligned (V 33%nat) 16 -> 0 <= (V 34%nat) <= 17179869184 -> 2 <= (V 35%nat) <= 8589934592 -> 4096 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + (V 35%nat) <= 2147446784) -> (65536 + 6864896 <= (V 33%nat) \/ (V 33%nat) + (V 35%nat) <= 65536) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 192) <= bv_unsigned a < ((V 2%nat) - 192) + 160) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 192) <= i < ((V 2%nat) - 192) + 160) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb13a0 M) (st fx' R' 0x136668 M')
        /\ (forall x, In x KS_bskS1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 726824
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 192)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 96)
        /\ getr R' (reg 9) = Z_to_bv 64 (2 * (V 35%nat))
        /\ getr R' (reg 10) = Z_to_bv 64 (2 * (V 35%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 1335544
        /\ getr R' (reg 13) = getr R (reg 10)
        /\ getr R' (reg 14) = Z_to_bv 64 4611686018427387903
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 ((((V 2%nat) - 96) / 8) + 2147450880)
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (bv_unsigned (getr R (reg 10)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((((bv_unsigned (getr R (reg 10))) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (bv_unsigned (getr R (reg 11)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (bv_unsigned (getr R (reg 10)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) ((bv_unsigned (getr R (reg 10))) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) 726092
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) ((V 33%nat) + (V 35%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) ((((bv_unsigned (getr R (reg 10))) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) ((bv_unsigned (getr R (reg 10))) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) 725624).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G1 G2 G8 G9 G12 G18 K0 K1 K2 pvzI7 K4 K5 K6 pvzI8 K8 K9 K10 K11 K12 pvzI9 K14 K15 K16 pvzI10 K18 K19 K20 K21 K22 pvzI11 K24 pvzI12 pvzI13 pvzI14 K28 K29.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV40l; move HV40l before pvzI5; pose proof (proj2 pvzI5) as HV40r; move HV40r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV57l; move HV57l before pvzI6; pose proof (proj2 pvzI6) as HV57r; move HV57r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K7l; move K7l before pvzI8; pose proof (proj2 pvzI8) as K7r; move K7r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K13l; move K13l before pvzI9; pose proof (proj2 pvzI9) as K13r; move K13r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K17l; move K17l before pvzI10; pose proof (proj2 pvzI10) as K17r; move K17r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K23l; move K23l before pvzI11; pose proof (proj2 pvzI11) as K23r; move K23r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K25l; move K25l before pvzI12; pose proof (proj2 pvzI12) as K25r; move K25r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K26l; move K26l before pvzI13; pose proof (proj2 pvzI13) as K26r; move K26r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K27l; move K27l before pvzI14; pose proof (proj2 pvzI14) as K27r; move K27r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 40%nat => Z_to_bv 64 vz_40 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 40%nat => vz_40 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbskS1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbskS1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbskS1.kn0).
  { unfold know_ok, PbskS1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18; lia | clear - HV2l HV2r K3l K3r K12 K18; lia | clear - HV2l HV2r K3l K3r K12 K18; lia | exactA K5]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18; lia | clear - HV2l HV2r K3l K3r K12 K18; lia | clear - HV2l HV2r K3l K3r K12 K18; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | evalEk ZA ltac:(clear) | clear - K7l K7r K9 K12 K19; lia | clear - K7l K7r K9 K12 K19; lia | clear - K7l K7r K9 K12 K19; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | evalEk ZA ltac:(clear) | clear - K7l K7r K9 K12 K19; lia | clear - K7l K7r K9 K12 K19; lia | clear - K7l K7r K9 K12 K19; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K13l K13r K14 K18 K19) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K13l K13r K14 K18 K19) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - K13l K13r K14 K18 K19) | evalEk ZA ltac:(clear) | clear - K13l K13r K14 K18 K19; lia | clear - K13l K13r K14 K18 K19; lia | clear - K13l K13r K14 K18 K19; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - K13l K13r K14 K18 K19) | evalEk ZA ltac:(clear - HV40l HV40r K17l K17r) | clear - K13l K13r K14 K18 K19; lia | clear - K13l K13r K14 K18 K19; lia | byte_tac ltac:(clear - HV40l HV40r K17l K17r) | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - K13l K13r K14 K18 K19) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - K13l K13r K14 K18 K19) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | evalEk ZA ltac:(clear - HV33l HV33r K23l K23r K27l K27r K28 K29) | clear - K7l K7r K9 K12 K19; lia | clear - K7l K7r K9 K12 K19; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | evalEk ZA ltac:(clear - HV33l HV33r K23l K23r K27l K27r K28 K29 HV35l HV35r K26l K26r) | clear - K7l K7r K9 K12 K19; lia | clear - K7l K7r K9 K12 K19; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K7l K7r K9 K12 K19) | evalEk ZA ltac:(clear - HV33l HV33r K23l K23r K27l K27r K28 K29 HV35l HV35r K26l K26r) | clear - K7l K7r K9 K12 K19; lia | clear - K7l K7r K9 K12 K19; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K23l K23r K27l K27r K28 K29) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K23l K23r K27l K27r K28 K29) | clear; lia | exact K24]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K26l K26r K27l K27r K28 K29) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K23l K23r K27l K27r K28 K29 HV35l HV35r K26l K26r) | exact (conj K27l K27r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K23l K23r K27l K27r K28 K29) | evalEk ZA ltac:(clear - HV35l HV35r K26l K26r K27l K27r K28 K29) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K23l K23r K27l K27r K28 K29) | evalEk ZA ltac:(clear - HV35l HV35r K26l K26r K27l K27r K28 K29) | generalize K29; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbskS1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbskS1.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 192) <= bv_unsigned a < (vz_2 - 192) + 160) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbskS1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbskS1.ps0) with 0x136668 in Hms. change (SR.ps_regs PbskS1.ps0) with (map (fun i => (i, nth i PbskS1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbskS1.ps0) with PbskS1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbskS1.regs0 PbskS1.regs_out0 60 KS_bskS1 KS_bskS1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbskS1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbskS1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS1.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbskS1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS1.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbskS1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS1.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbskS1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbskS1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbskS1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbskS1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS1.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbskS1.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PbskS1.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbskS1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS1.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbskS1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS1.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbskS1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS1.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbskS1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS1.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbskS1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - K7l K7r K9 K12 K19) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - K7l K7r K9 K12 K19) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - K13l K13r K14 K18 K19) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - K7l K7r K9 K12 K19) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - K7l K7r K9 K12 K19) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K23l K23r K27l K27r K28 K29 HV35l HV35r K26l K26r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - K7l K7r K9 K12 K19) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - K7l K7r K9 K12 K19) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PbskT := BndP_Eb_049S9.LibSegEb_bskT.
Definition KS_bskT : list nat := Eval vm_compute in (BG.kept_list 60 PbskT.regs0 PbskT.regs_out0).
Lemma KS_bskT_ok : BG.kept_ok 60 PbskT.regs0 PbskT.regs_out0 KS_bskT = true. Proof. vm_compute. reflexivity. Qed.
Lemma bskT_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 9) = Z_to_bv 64 (V 38%nat) -> getr R (reg 10) = Z_to_bv 64 (V 37%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 120) -> getr R (reg 19) = Z_to_bv 64 (V 34%nat) -> getr R (reg 20) = Z_to_bv 64 ((((V 2%nat) - 96) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 -> 4096 <= (V 37%nat) <= 140737488355328 ->
  0 <= (V 34%nat) <= 17179869184 -> 1 <= (V 38%nat) <= 17179869184 -> 4096 <= ((V 37%nat) + (V 38%nat)) <= 140737488355328 -> 4096 <= ((V 34%nat) + (V 37%nat)) <= 140737488355328 ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) 726092 -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 39%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 43%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 168) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 176) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 184) (V 52%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 120) <= bv_unsigned a < ((V 2%nat) - 120) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 120) <= i < ((V 2%nat) - 120) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1728 M) (st fx' R' 0xb17cc M')
        /\ (forall x, In x KS_bskT -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 726092
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 39%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) ((V 37%nat) + (V 38%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) ((V 34%nat) + (V 37%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) ((V 34%nat) + (V 37%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (V 37%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 K0 K1 K2 pvzI13 K4 K5 K6 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 K12 K13 K14 K15 K16 K17 K18.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV34l; move HV34l before pvzI2; pose proof (proj2 pvzI2) as HV34r; move HV34r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV42l; move HV42l before pvzI6; pose proof (proj2 pvzI6) as HV42r; move HV42r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV43l; move HV43l before pvzI7; pose proof (proj2 pvzI7) as HV43r; move HV43r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV48l; move HV48l before pvzI8; pose proof (proj2 pvzI8) as HV48r; move HV48r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV49l; move HV49l before pvzI9; pose proof (proj2 pvzI9) as HV49r; move HV49r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV52l; move HV52l before pvzI10; pose proof (proj2 pvzI10) as HV52r; move HV52r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV56l; move HV56l before pvzI11; pose proof (proj2 pvzI11) as HV56r; move HV56r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV57l; move HV57l before pvzI12; pose proof (proj2 pvzI12) as HV57r; move HV57r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K3l; move K3l before pvzI13; pose proof (proj2 pvzI13) as K3r; move K3r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K7l; move K7l before pvzI14; pose proof (proj2 pvzI14) as K7r; move K7r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K8l; move K8l before pvzI15; pose proof (proj2 pvzI15) as K8r; move K8r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K9l; move K9l before pvzI16; pose proof (proj2 pvzI16) as K9r; move K9r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K10l; move K10l before pvzI17; pose proof (proj2 pvzI17) as K10r; move K10r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K11l; move K11l before pvzI18; pose proof (proj2 pvzI18) as K11r; move K11r before pvzI18; clear pvzI18.
  set (vz_2 := V 2%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 34%nat => Z_to_bv 64 vz_34 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 52%nat => Z_to_bv 64 vz_52 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 34%nat => vz_34 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 42%nat => vz_42 | 43%nat => vz_43 | 48%nat => vz_48 | 49%nat => vz_49 | 52%nat => vz_52 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbskT.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbskT.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbskT.kn0).
  { unfold know_ok, PbskT.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K7l K7r K10l K10r K11l K11r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K8l K8r K11l K11r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K9l K9r K10l K10r) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K7l K7r K10l K10r K11l K11r HV38l HV38r K9l K9r) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K8l K8r K11l K11r HV37l HV37r K7l K7r K10l K10r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV39l HV39r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K18]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbskT.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbskT.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 120) <= bv_unsigned a < (vz_2 - 120) + 32) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbskT.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbskT.ps0) with 0xb17cc in Hms. change (SR.ps_regs PbskT.ps0) with (map (fun i => (i, nth i PbskT.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbskT.ps0) with PbskT.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbskT.regs0 PbskT.regs_out0 60 KS_bskT KS_bskT_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbskT.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbskT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskT.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbskT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskT.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbskT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskT.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbskT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskT.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbskT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskT.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbskT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskT.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbskT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskT.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbskT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskT.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbskT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskT.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbskT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskT.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbskT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskT.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbskT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K7l K7r K10l K10r K11l K11r HV38l HV38r K9l K9r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K8l K8r K11l K11r HV37l HV37r K7l K7r K10l K10r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K8l K8r K11l K11r HV37l HV37r K7l K7r K10l K10r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K7l K7r K10l K10r K11l K11r) | clear; lia].
Qed.

Module PbskUz := BndP_Eb_049S9.LibSegEb_bskUz.
Definition KS_bskUz : list nat := Eval vm_compute in (BG.kept_list 60 PbskUz.regs0 PbskUz.regs_out0).
Lemma KS_bskUz_ok : BG.kept_ok 60 PbskUz.regs0 PbskUz.regs_out0 KS_bskUz = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma bskUz_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 9) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 ((((V 10%nat) + 8) / 8) + 2147450880) -> getr R (reg 20) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 -> 6930432 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 10%nat) 24 ->
  (((V 2%nat) - 256) + 256 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 256)) -> 4096 <= (V 36%nat) <= 140737488355327 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 1 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 1 ->
  L5.u8_at RSEGS M (V 36%nat) (V 40%nat) -> 0 <= (V 40%nat) <= 255 -> ((V 36%nat) + 1 <= ((V 2%nat) - 256) \/ ((V 2%nat) - 256) + 256 <= (V 36%nat)) -> ((V 36%nat) + 1 <= (V 10%nat) \/ (V 10%nat) + 24 <= (V 36%nat)) ->
  4096 <= (V 37%nat) <= 140737488355328 -> aligned (V 37%nat) 16 -> 4096 <= ((V 37%nat) + 1) <= 140737488355328 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 1 <= 2147446784) ->
  (65536 + 6864896 <= (V 37%nat) \/ (V 37%nat) + 1 <= 65536) -> L5.writable RSEGS M (V 37%nat) 1 -> (((V 2%nat) - 256) + 256 <= (V 37%nat) \/ (V 37%nat) + 1 <= ((V 2%nat) - 256)) -> ((V 10%nat) + 24 <= (V 37%nat) \/ (V 37%nat) + 1 <= (V 10%nat)) ->
  ((V 36%nat) + 1 <= (V 37%nat) \/ (V 37%nat) + 1 <= (V 36%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 120) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 112) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 37%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 96) ((V 37%nat) + 1) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 10%nat) -> L5.u8_at RSEGS M (((V 37%nat) / 8) + 2147450880) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 37%nat) + 0) <= bv_unsigned a < ((V 37%nat) + 0) + 1) -> ~ (((V 2%nat) - 104) <= bv_unsigned a < ((V 2%nat) - 104) + 8) -> ~ (((V 2%nat) - 208) <= bv_unsigned a < ((V 2%nat) - 208) + 80) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 37%nat) + 0) <= i < ((V 37%nat) + 0) + 1) -> ~ (((V 2%nat) - 104) <= i < ((V 2%nat) - 104) + 8) -> ~ (((V 2%nat) - 208) <= i < ((V 2%nat) - 208) + 80) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb144c M) (st fx' R' 0xab190 M')
        /\ (forall x, In x KS_bskUz -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 727108
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 208)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 10%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1335544
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((((V 10%nat) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 10%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) ((V 10%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) 726172
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) ((V 37%nat) + 1)
        /\ L5.u8_at RSEGS M' (V 37%nat) (V 40%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G10 G11 G12 G18 G19 G20 K0 K1 K2 pvzI9 K4 K5 K6 pvzI10 K8 K9 K10 K11 K12 pvzI11 K14 K15 K16 pvzI12 K18 K19 pvzI13 K21 pvzI14 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV40l; move HV40l before pvzI5; pose proof (proj2 pvzI5) as HV40r; move HV40r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV55l; move HV55l before pvzI6; pose proof (proj2 pvzI6) as HV55r; move HV55r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV56l; move HV56l before pvzI7; pose proof (proj2 pvzI7) as HV56r; move HV56r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV57l; move HV57l before pvzI8; pose proof (proj2 pvzI8) as HV57r; move HV57r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K7l; move K7l before pvzI10; pose proof (proj2 pvzI10) as K7r; move K7r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K13l; move K13l before pvzI11; pose proof (proj2 pvzI11) as K13r; move K13r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K17l; move K17l before pvzI12; pose proof (proj2 pvzI12) as K17r; move K17r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K20l; move K20l before pvzI13; pose proof (proj2 pvzI13) as K20r; move K20r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K22l; move K22l before pvzI14; pose proof (proj2 pvzI14) as K22r; move K22r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 40%nat => Z_to_bv 64 vz_40 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 36%nat => vz_36 | 37%nat => vz_37 | 40%nat => vz_40 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbskUz.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbskUz.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbskUz.kn0).
  { unfold know_ok, PbskUz.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | exactA K5]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K7l K7r K9 K12 K19 K27; lia | clear - HV10l HV10r K7l K7r K9 K12 K19 K27; lia | clear - HV10l HV10r K7l K7r K9 K12 K19 K27; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K7l K7r K9 K12 K19 K27; lia | clear - HV10l HV10r K7l K7r K9 K12 K19 K27; lia | clear - HV10l HV10r K7l K7r K9 K12 K19 K27; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K28) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K28) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K28) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K13l K13r K14 K18 K19 K28; lia | clear - HV36l HV36r K13l K13r K14 K18 K19 K28; lia | clear - HV36l HV36r K13l K13r K14 K18 K19 K28; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K28) | evalEk ZA ltac:(clear - HV40l HV40r K17l K17r) | clear - HV36l HV36r K13l K13r K14 K18 K19 K28; lia | clear - HV36l HV36r K13l K13r K14 K18 K19 K28; lia | byte_tac ltac:(clear - HV40l HV40r K17l K17r) | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | clear; lia | exact K21]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28; lia | clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28; lia | clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28; lia | clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28; lia | byte_tac ltac:(clear) | exactA K34]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbskUz.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbskUz.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_37 + 0) <= bv_unsigned a < (vz_37 + 0) + 1) -> ~ ((vz_2 - 104) <= bv_unsigned a < (vz_2 - 104) + 8) -> ~ ((vz_2 - 208) <= bv_unsigned a < (vz_2 - 208) + 80) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PbskUz.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk' ZA Hag ltac:(clear) | clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18 K26 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18 K26 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbskUz.ps0) with 0xab190 in Hms. change (SR.ps_regs PbskUz.ps0) with (map (fun i => (i, nth i PbskUz.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbskUz.ps0) with PbskUz.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbskUz.regs0 PbskUz.regs_out0 60 KS_bskUz KS_bskUz_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbskUz.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbskUz.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskUz.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbskUz.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskUz.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbskUz.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskUz.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbskUz.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskUz.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbskUz.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskUz.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbskUz.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskUz.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbskUz.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskUz.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbskUz.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K28) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K17l K17r) | byte_tac ltac:(clear - HV40l HV40r K17l K17r) | clear; lia].
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PbskUo := BndP_Eb_049S9.LibSegEb_bskUo.
Definition KS_bskUo : list nat := Eval vm_compute in (BG.kept_list 60 PbskUo.regs0 PbskUo.regs_out0).
Lemma KS_bskUo_ok : BG.kept_ok 60 PbskUo.regs0 PbskUo.regs_out0 KS_bskUo = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma bskUo_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 9) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 ((((V 10%nat) + 8) / 8) + 2147450880) -> getr R (reg 20) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 -> 6930432 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 10%nat) 24 ->
  (((V 2%nat) - 256) + 256 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 256)) -> 4096 <= (V 36%nat) <= 140737488355327 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 1 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 1 ->
  L5.u8_at RSEGS M (V 36%nat) (V 40%nat) -> 0 <= (V 40%nat) <= 255 -> ((V 36%nat) + 1 <= ((V 2%nat) - 256) \/ ((V 2%nat) - 256) + 256 <= (V 36%nat)) -> ((V 36%nat) + 1 <= (V 10%nat) \/ (V 10%nat) + 24 <= (V 36%nat)) ->
  4096 <= (V 37%nat) <= 140737488355328 -> aligned (V 37%nat) 16 -> 4096 <= ((V 37%nat) + 2) <= 140737488355328 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 2 <= 2147446784) ->
  (65536 + 6864896 <= (V 37%nat) \/ (V 37%nat) + 2 <= 65536) -> L5.writable RSEGS M (V 37%nat) 2 -> (((V 2%nat) - 256) + 256 <= (V 37%nat) \/ (V 37%nat) + 2 <= ((V 2%nat) - 256)) -> ((V 10%nat) + 24 <= (V 37%nat) \/ (V 37%nat) + 2 <= (V 10%nat)) ->
  ((V 36%nat) + 1 <= (V 37%nat) \/ (V 37%nat) + 2 <= (V 36%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 120) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 37%nat) + 1) -> L5.u64_at RSEGS M ((V 2%nat) - 104) ((V 37%nat) + 1) ->
  L5.u64_at RSEGS M ((V 2%nat) - 96) ((V 37%nat) + 2) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 10%nat) -> L5.u8_at RSEGS M ((((V 37%nat) + 1) / 8) + 2147450880) 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 37%nat) + 1) <= bv_unsigned a < ((V 37%nat) + 1) + 1) -> ~ (((V 2%nat) - 104) <= bv_unsigned a < ((V 2%nat) - 104) + 8) -> ~ (((V 2%nat) - 208) <= bv_unsigned a < ((V 2%nat) - 208) + 80) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 37%nat) + 1) <= i < ((V 37%nat) + 1) + 1) -> ~ (((V 2%nat) - 104) <= i < ((V 2%nat) - 104) + 8) -> ~ (((V 2%nat) - 208) <= i < ((V 2%nat) - 208) + 80) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb144c M) (st fx' R' 0xab190 M')
        /\ (forall x, In x KS_bskUo -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 727108
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 208)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 10%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1335544
        /\ getr R' (reg 12) = Z_to_bv 64 2
        /\ getr R' (reg 13) = Z_to_bv 64 1
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((((V 10%nat) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 10%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) ((V 10%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) 726172
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) ((V 37%nat) + 2)
        /\ L5.u8_at RSEGS M' ((V 37%nat) + 1) (V 40%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G10 G11 G12 G18 G19 G20 K0 K1 K2 pvzI9 K4 K5 K6 pvzI10 K8 K9 K10 K11 K12 pvzI11 K14 K15 K16 pvzI12 K18 K19 pvzI13 K21 pvzI14 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV40l; move HV40l before pvzI5; pose proof (proj2 pvzI5) as HV40r; move HV40r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV55l; move HV55l before pvzI6; pose proof (proj2 pvzI6) as HV55r; move HV55r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV56l; move HV56l before pvzI7; pose proof (proj2 pvzI7) as HV56r; move HV56r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV57l; move HV57l before pvzI8; pose proof (proj2 pvzI8) as HV57r; move HV57r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K7l; move K7l before pvzI10; pose proof (proj2 pvzI10) as K7r; move K7r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K13l; move K13l before pvzI11; pose proof (proj2 pvzI11) as K13r; move K13r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K17l; move K17l before pvzI12; pose proof (proj2 pvzI12) as K17r; move K17r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K20l; move K20l before pvzI13; pose proof (proj2 pvzI13) as K20r; move K20r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K22l; move K22l before pvzI14; pose proof (proj2 pvzI14) as K22r; move K22r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 40%nat => Z_to_bv 64 vz_40 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 36%nat => vz_36 | 37%nat => vz_37 | 40%nat => vz_40 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbskUo.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbskUo.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbskUo.kn0).
  { unfold know_ok, PbskUo.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | exactA K5]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K7l K7r K9 K12 K19 K27; lia | clear - HV10l HV10r K7l K7r K9 K12 K19 K27; lia | clear - HV10l HV10r K7l K7r K9 K12 K19 K27; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K7l K7r K9 K12 K19 K27; lia | clear - HV10l HV10r K7l K7r K9 K12 K19 K27; lia | clear - HV10l HV10r K7l K7r K9 K12 K19 K27; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K28) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K28) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K28) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K13l K13r K14 K18 K19 K28; lia | clear - HV36l HV36r K13l K13r K14 K18 K19 K28; lia | clear - HV36l HV36r K13l K13r K14 K18 K19 K28; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K28) | evalEk ZA ltac:(clear - HV40l HV40r K17l K17r) | clear - HV36l HV36r K13l K13r K14 K18 K19 K28; lia | clear - HV36l HV36r K13l K13r K14 K18 K19 K28; lia | byte_tac ltac:(clear - HV40l HV40r K17l K17r) | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | clear; lia | exact K21]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28; lia | clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28; lia | clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28; lia | clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28; lia | byte_tac ltac:(clear) | exactA K34]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbskUo.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbskUo.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_37 + 1) <= bv_unsigned a < (vz_37 + 1) + 1) -> ~ ((vz_2 - 104) <= bv_unsigned a < (vz_2 - 104) + 8) -> ~ ((vz_2 - 208) <= bv_unsigned a < (vz_2 - 208) + 80) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PbskUo.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk' ZA Hag ltac:(clear) | clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18 K26 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18 K26 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbskUo.ps0) with 0xab190 in Hms. change (SR.ps_regs PbskUo.ps0) with (map (fun i => (i, nth i PbskUo.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbskUo.ps0) with PbskUo.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbskUo.regs0 PbskUo.regs_out0 60 KS_bskUo KS_bskUo_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbskUo.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbskUo.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskUo.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbskUo.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskUo.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbskUo.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskUo.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbskUo.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskUo.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbskUo.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskUo.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbskUo.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskUo.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbskUo.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskUo.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbskUo.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K28) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K17l K17r) | byte_tac ltac:(clear - HV40l HV40r K17l K17r) | clear; lia].
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PbskUt := BndP_Eb_049S9.LibSegEb_bskUt.
Definition KS_bskUt : list nat := Eval vm_compute in (BG.kept_list 60 PbskUt.regs0 PbskUt.regs_out0).
Lemma KS_bskUt_ok : BG.kept_ok 60 PbskUt.regs0 PbskUt.regs_out0 KS_bskUt = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma bskUt_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 9) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 ((((V 10%nat) + 8) / 8) + 2147450880) -> getr R (reg 20) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 -> 6930432 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 10%nat) 24 ->
  (((V 2%nat) - 256) + 256 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 256)) -> 4096 <= (V 36%nat) <= 140737488355327 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 1 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 1 ->
  L5.u8_at RSEGS M (V 36%nat) (V 40%nat) -> 0 <= (V 40%nat) <= 255 -> ((V 36%nat) + 1 <= ((V 2%nat) - 256) \/ ((V 2%nat) - 256) + 256 <= (V 36%nat)) -> ((V 36%nat) + 1 <= (V 10%nat) \/ (V 10%nat) + 24 <= (V 36%nat)) ->
  4096 <= (V 37%nat) <= 140737488355328 -> aligned (V 37%nat) 16 -> 4096 <= ((V 37%nat) + 4) <= 140737488355328 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 4 <= 2147446784) ->
  (65536 + 6864896 <= (V 37%nat) \/ (V 37%nat) + 4 <= 65536) -> L5.writable RSEGS M (V 37%nat) 4 -> (((V 2%nat) - 256) + 256 <= (V 37%nat) \/ (V 37%nat) + 4 <= ((V 2%nat) - 256)) -> ((V 10%nat) + 24 <= (V 37%nat) \/ (V 37%nat) + 4 <= (V 10%nat)) ->
  ((V 36%nat) + 1 <= (V 37%nat) \/ (V 37%nat) + 4 <= (V 36%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 120) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 37%nat) + 2) -> L5.u64_at RSEGS M ((V 2%nat) - 104) ((V 37%nat) + 2) ->
  L5.u64_at RSEGS M ((V 2%nat) - 96) ((V 37%nat) + 4) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 10%nat) -> L5.u8_at RSEGS M ((((V 37%nat) + 2) / 8) + 2147450880) 4 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 37%nat) + 2) <= bv_unsigned a < ((V 37%nat) + 2) + 1) -> ~ (((V 2%nat) - 104) <= bv_unsigned a < ((V 2%nat) - 104) + 8) -> ~ (((V 2%nat) - 208) <= bv_unsigned a < ((V 2%nat) - 208) + 80) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 37%nat) + 2) <= i < ((V 37%nat) + 2) + 1) -> ~ (((V 2%nat) - 104) <= i < ((V 2%nat) - 104) + 8) -> ~ (((V 2%nat) - 208) <= i < ((V 2%nat) - 208) + 80) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb144c M) (st fx' R' 0xab190 M')
        /\ (forall x, In x KS_bskUt -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 727108
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 208)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 10%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1335544
        /\ getr R' (reg 12) = Z_to_bv 64 4
        /\ getr R' (reg 13) = Z_to_bv 64 2
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((((V 10%nat) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 10%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) ((V 10%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) 726172
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) ((V 37%nat) + 3)
        /\ L5.u8_at RSEGS M' ((V 37%nat) + 2) (V 40%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G10 G11 G12 G18 G19 G20 K0 K1 K2 pvzI9 K4 K5 K6 pvzI10 K8 K9 K10 K11 K12 pvzI11 K14 K15 K16 pvzI12 K18 K19 pvzI13 K21 pvzI14 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV40l; move HV40l before pvzI5; pose proof (proj2 pvzI5) as HV40r; move HV40r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV55l; move HV55l before pvzI6; pose proof (proj2 pvzI6) as HV55r; move HV55r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV56l; move HV56l before pvzI7; pose proof (proj2 pvzI7) as HV56r; move HV56r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV57l; move HV57l before pvzI8; pose proof (proj2 pvzI8) as HV57r; move HV57r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K7l; move K7l before pvzI10; pose proof (proj2 pvzI10) as K7r; move K7r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K13l; move K13l before pvzI11; pose proof (proj2 pvzI11) as K13r; move K13r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K17l; move K17l before pvzI12; pose proof (proj2 pvzI12) as K17r; move K17r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K20l; move K20l before pvzI13; pose proof (proj2 pvzI13) as K20r; move K20r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K22l; move K22l before pvzI14; pose proof (proj2 pvzI14) as K22r; move K22r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 40%nat => Z_to_bv 64 vz_40 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 36%nat => vz_36 | 37%nat => vz_37 | 40%nat => vz_40 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbskUt.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbskUt.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbskUt.kn0).
  { unfold know_ok, PbskUt.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | exactA K5]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K7l K7r K9 K12 K19 K27; lia | clear - HV10l HV10r K7l K7r K9 K12 K19 K27; lia | clear - HV10l HV10r K7l K7r K9 K12 K19 K27; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K7l K7r K9 K12 K19 K27; lia | clear - HV10l HV10r K7l K7r K9 K12 K19 K27; lia | clear - HV10l HV10r K7l K7r K9 K12 K19 K27; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K28) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K28) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K28) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K13l K13r K14 K18 K19 K28; lia | clear - HV36l HV36r K13l K13r K14 K18 K19 K28; lia | clear - HV36l HV36r K13l K13r K14 K18 K19 K28; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K28) | evalEk ZA ltac:(clear - HV40l HV40r K17l K17r) | clear - HV36l HV36r K13l K13r K14 K18 K19 K28; lia | clear - HV36l HV36r K13l K13r K14 K18 K19 K28; lia | byte_tac ltac:(clear - HV40l HV40r K17l K17r) | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | clear; lia | exact K21]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28; lia | clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28; lia | clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28; lia | clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28; lia | byte_tac ltac:(clear) | exactA K34]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbskUt.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbskUt.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_37 + 2) <= bv_unsigned a < (vz_37 + 2) + 1) -> ~ ((vz_2 - 104) <= bv_unsigned a < (vz_2 - 104) + 8) -> ~ ((vz_2 - 208) <= bv_unsigned a < (vz_2 - 208) + 80) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PbskUt.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk' ZA Hag ltac:(clear) | clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18 K26 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18 K26 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbskUt.ps0) with 0xab190 in Hms. change (SR.ps_regs PbskUt.ps0) with (map (fun i => (i, nth i PbskUt.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbskUt.ps0) with PbskUt.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbskUt.regs0 PbskUt.regs_out0 60 KS_bskUt KS_bskUt_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbskUt.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbskUt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskUt.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbskUt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskUt.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbskUt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskUt.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbskUt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskUt.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbskUt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskUt.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbskUt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskUt.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbskUt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskUt.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbskUt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K28) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K17l K17r) | byte_tac ltac:(clear - HV40l HV40r K17l K17r) | clear; lia].
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PbskU := BndP_Eb_049S9.LibSegEb_bskU.
Definition KS_bskU : list nat := Eval vm_compute in (BG.kept_list 60 PbskU.regs0 PbskU.regs_out0).
Lemma KS_bskU_ok : BG.kept_ok 60 PbskU.regs0 PbskU.regs_out0 KS_bskU = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma bskU_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 9) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 ((((V 10%nat) + 8) / 8) + 2147450880) -> getr R (reg 20) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 -> 6930432 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 10%nat) 24 ->
  (((V 2%nat) - 256) + 256 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 256)) -> 4096 <= (V 36%nat) <= 140737488355327 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 1 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 1 ->
  L5.u8_at RSEGS M (V 36%nat) (V 40%nat) -> 0 <= (V 40%nat) <= 255 -> ((V 36%nat) + 1 <= ((V 2%nat) - 256) \/ ((V 2%nat) - 256) + 256 <= (V 36%nat)) -> ((V 36%nat) + 1 <= (V 10%nat) \/ (V 10%nat) + 24 <= (V 36%nat)) ->
  4096 <= (V 37%nat) <= 140737488355328 -> aligned (V 37%nat) 16 -> 4096 <= ((V 37%nat) + (V 38%nat)) <= 140737488355328 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + (V 38%nat) <= 2147446784) ->
  (65536 + 6864896 <= (V 37%nat) \/ (V 37%nat) + (V 38%nat) <= 65536) -> L5.writable RSEGS M (V 37%nat) (V 38%nat) -> (((V 2%nat) - 256) + 256 <= (V 37%nat) \/ (V 37%nat) + (V 38%nat) <= ((V 2%nat) - 256)) -> ((V 10%nat) + 24 <= (V 37%nat) \/ (V 37%nat) + (V 38%nat) <= (V 10%nat)) ->
  ((V 36%nat) + 1 <= (V 37%nat) \/ (V 37%nat) + (V 38%nat) <= (V 36%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 120) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 34%nat) + (V 37%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 104) ((V 34%nat) + (V 37%nat)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 96) ((V 37%nat) + (V 38%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 10%nat) -> 4 <= (V 34%nat) <= 8589934592 -> 8 <= (V 38%nat) <= 17179869184 ->
  4 <= ((V 38%nat) - (V 34%nat)) <= 17179869184 -> L5KA.zeros_at M ((((V 34%nat) + (V 37%nat)) / 8) + 2147450880) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((((V 34%nat) + (V 37%nat)) + 0) <= bv_unsigned a < (((V 34%nat) + (V 37%nat)) + 0) + 1) -> ~ (((V 2%nat) - 104) <= bv_unsigned a < ((V 2%nat) - 104) + 8) -> ~ (((V 2%nat) - 208) <= bv_unsigned a < ((V 2%nat) - 208) + 80) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((((V 34%nat) + (V 37%nat)) + 0) <= i < (((V 34%nat) + (V 37%nat)) + 0) + 1) -> ~ (((V 2%nat) - 104) <= i < ((V 2%nat) - 104) + 8) -> ~ (((V 2%nat) - 208) <= i < ((V 2%nat) - 208) + 80) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb144c M) (st fx' R' 0xab190 M')
        /\ (forall x, In x KS_bskU -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 727108
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 208)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 10%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1335544
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((((V 10%nat) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 10%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) ((V 10%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) 726172
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (((V 34%nat) + (V 37%nat)) + 1)
        /\ L5.u8_at RSEGS M' ((V 34%nat) + (V 37%nat)) (V 40%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 G2 G8 G9 G10 G11 G12 G18 G19 G20 K0 K1 K2 pvzI11 K4 K5 K6 pvzI12 K8 K9 K10 K11 K12 pvzI13 K14 K15 K16 pvzI14 K18 K19 pvzI15 K21 pvzI16 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 pvzI17 pvzI18 pvzI19 K37.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV40l; move HV40l before pvzI7; pose proof (proj2 pvzI7) as HV40r; move HV40r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV55l; move HV55l before pvzI8; pose proof (proj2 pvzI8) as HV55r; move HV55r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV56l; move HV56l before pvzI9; pose proof (proj2 pvzI9) as HV56r; move HV56r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV57l; move HV57l before pvzI10; pose proof (proj2 pvzI10) as HV57r; move HV57r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K3l; move K3l before pvzI11; pose proof (proj2 pvzI11) as K3r; move K3r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K7l; move K7l before pvzI12; pose proof (proj2 pvzI12) as K7r; move K7r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K13l; move K13l before pvzI13; pose proof (proj2 pvzI13) as K13r; move K13r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K17l; move K17l before pvzI14; pose proof (proj2 pvzI14) as K17r; move K17r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K20l; move K20l before pvzI15; pose proof (proj2 pvzI15) as K20r; move K20r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K22l; move K22l before pvzI16; pose proof (proj2 pvzI16) as K22r; move K22r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K34l; move K34l before pvzI17; pose proof (proj2 pvzI17) as K34r; move K34r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K35l; move K35l before pvzI18; pose proof (proj2 pvzI18) as K35r; move K35r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K36l; move K36l before pvzI19; pose proof (proj2 pvzI19) as K36r; move K36r before pvzI19; clear pvzI19.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 40%nat => Z_to_bv 64 vz_40 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 34%nat => vz_34 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 40%nat => vz_40 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbskU.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbskU.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbskU.kn0).
  { unfold know_ok, PbskU.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | exactA K5]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K7l K7r K9 K12 K19 K27; lia | clear - HV10l HV10r K7l K7r K9 K12 K19 K27; lia | clear - HV10l HV10r K7l K7r K9 K12 K19 K27; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K7l K7r K9 K12 K19 K27; lia | clear - HV10l HV10r K7l K7r K9 K12 K19 K27; lia | clear - HV10l HV10r K7l K7r K9 K12 K19 K27; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K28) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K28) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K28) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K13l K13r K14 K18 K19 K28; lia | clear - HV36l HV36r K13l K13r K14 K18 K19 K28; lia | clear - HV36l HV36r K13l K13r K14 K18 K19 K28; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K28) | evalEk ZA ltac:(clear - HV40l HV40r K17l K17r) | clear - HV36l HV36r K13l K13r K14 K18 K19 K28; lia | clear - HV36l HV36r K13l K13r K14 K18 K19 K28; lia | byte_tac ltac:(clear - HV40l HV40r K17l K17r) | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | clear; lia | exact K21]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28 HV38l HV38r K35l K35r K36l K36r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk ZA ltac:(clear - HV38l HV38r K22l K22r K23 K24 K26 K27 K28 K35l K35r K36l K36r) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk ZA ltac:(clear - HV38l HV38r K22l K22r K23 K24 K26 K27 K28 K35l K35r K36l K36r) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk ZA ltac:(clear - HV38l HV38r K22l K22r K23 K24 K26 K27 K28 K35l K35r K36l K36r) | clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28 HV38l HV38r K35l K35r K36l K36r; lia | clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28 HV38l HV38r K35l K35r K36l K36r; lia | clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28 HV38l HV38r K35l K35r K36l K36r; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk ZA ltac:(clear - HV38l HV38r K22l K22r K23 K24 K26 K27 K28 K35l K35r K36l K36r) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk ZA ltac:(clear - HV38l HV38r K22l K22r K23 K24 K26 K27 K28 K35l K35r K36l K36r) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk ZA ltac:(clear - HV38l HV38r K22l K22r K23 K24 K26 K27 K28 K35l K35r K36l K36r) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk ZA ltac:(clear - HV34l HV34r K34l K34r K36l K36r HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk ZA ltac:(clear - HV34l HV34r K34l K34r K36l K36r HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28 HV38l HV38r K35l K35r K36l K36r) | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | clear - HV2l HV2r K3l K3r K12 K18 K26; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K34l K34r K36l K36r) | exact (conj K34l K34r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K22l K22r K23 K24 K26 K27 K28 K35l K35r K36l K36r) | exact (conj K35l K35r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K34l K34r K36l K36r HV38l HV38r K22l K22r K23 K24 K26 K27 K28 K35l K35r) | exact (conj K36l K36r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K34l K34r K36l K36r HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K34l K34r K36l K36r HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28; lia | clear - HV34l HV34r K34l K34r K36l K36r HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28; lia | clear - HV34l HV34r K34l K34r K36l K36r HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28; lia | exactA K37]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbskU.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbskU.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((vz_34 + vz_37) + 0) <= bv_unsigned a < ((vz_34 + vz_37) + 0) + 1) -> ~ ((vz_2 - 104) <= bv_unsigned a < (vz_2 - 104) + 8) -> ~ ((vz_2 - 208) <= bv_unsigned a < (vz_2 - 208) + 80) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PbskU.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV34l HV34r K34l K34r K36l K36r HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk' ZA Hag ltac:(clear) | clear - HV34l HV34r K34l K34r K36l K36r HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18 K26 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18 K26 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbskU.ps0) with 0xab190 in Hms. change (SR.ps_regs PbskU.ps0) with (map (fun i => (i, nth i PbskU.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbskU.ps0) with PbskU.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbskU.regs0 PbskU.regs_out0 60 KS_bskU KS_bskU_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbskU.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbskU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskU.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbskU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskU.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbskU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskU.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbskU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskU.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbskU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskU.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbskU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskU.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbskU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K28) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K34l K34r K36l K36r HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV34l HV34r K34l K34r K36l K36r HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K17l K17r) | byte_tac ltac:(clear - HV40l HV40r K17l K17r) | clear; lia].
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PbskW2 := BndP_Eb_050S9.LibSegEb_bskW2.
Definition KS_bskW2 : list nat := Eval vm_compute in (BG.kept_list 60 PbskW2.regs0 PbskW2.regs_out0).
Lemma KS_bskW2_ok : BG.kept_ok 60 PbskW2.regs0 PbskW2.regs_out0 KS_bskW2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bskW2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 208) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 120) -> getr R (reg 9) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 -> 6930432 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 10%nat) 24 ->
  (((V 2%nat) - 256) + 256 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 256)) -> L5.u64_at RSEGS M (V 10%nat) (V 33%nat) -> L5.u64_at RSEGS M ((V 10%nat) + 8) ((V 33%nat) + (V 34%nat)) -> L5.u64_at RSEGS M ((V 10%nat) + 16) ((V 33%nat) + (V 35%nat)) ->
  1 <= (V 34%nat) <= 17179869184 -> 0 <= (V 33%nat) <= 140737488355328 -> 0 <= (V 34%nat) <= 17179869184 -> 0 <= (V 35%nat) <= 17179869184 ->
  0 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u64_at RSEGS M ((V 2%nat) - 120) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 34%nat) + (V 37%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (((V 34%nat) + (V 37%nat)) + 1) ->
  L5.u64_at RSEGS M ((V 2%nat) - 96) ((V 37%nat) + (V 38%nat)) -> 4096 <= (V 37%nat) <= 140737488355328 -> 4096 <= ((V 34%nat) + (V 37%nat)) <= 140737488355327 -> 4096 <= ((V 37%nat) + (V 38%nat)) <= 140737488355328 ->
  1 <= (V 38%nat) <= 17179869184 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1844 M) (st fx' R' 0x78e40 M')
        /\ (forall x, In x KS_bskW2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 727228
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 1
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 10%nat) + 8)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 2%nat) - 112)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 ((((V 10%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 23) = Z_to_bv 64 ((((V 2%nat) - 112) / 8) + 2147450880)
        /\ getr R' (reg 24) = Z_to_bv 64 (((V 10%nat) / 8) + 2147450880)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 G2 G8 G9 G10 G11 G12 G21 K0 K1 K2 pvzI11 K4 K5 K6 pvzI12 K8 K9 K10 K11 K12 K13 K14 K15 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 K21 K22 K23 K24 pvzI18 pvzI19 pvzI20 pvzI21.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV35l; move HV35l before pvzI5; pose proof (proj2 pvzI5) as HV35r; move HV35r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV37l; move HV37l before pvzI6; pose proof (proj2 pvzI6) as HV37r; move HV37r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV38l; move HV38l before pvzI7; pose proof (proj2 pvzI7) as HV38r; move HV38r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV55l; move HV55l before pvzI8; pose proof (proj2 pvzI8) as HV55r; move HV55r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV56l; move HV56l before pvzI9; pose proof (proj2 pvzI9) as HV56r; move HV56r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV57l; move HV57l before pvzI10; pose proof (proj2 pvzI10) as HV57r; move HV57r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K3l; move K3l before pvzI11; pose proof (proj2 pvzI11) as K3r; move K3r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K7l; move K7l before pvzI12; pose proof (proj2 pvzI12) as K7r; move K7r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K16l; move K16l before pvzI13; pose proof (proj2 pvzI13) as K16r; move K16r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K17l; move K17l before pvzI14; pose proof (proj2 pvzI14) as K17r; move K17r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K18l; move K18l before pvzI15; pose proof (proj2 pvzI15) as K18r; move K18r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K19l; move K19l before pvzI16; pose proof (proj2 pvzI16) as K19r; move K19r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K20l; move K20l before pvzI17; pose proof (proj2 pvzI17) as K20r; move K20r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K25l; move K25l before pvzI18; pose proof (proj2 pvzI18) as K25r; move K25r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K26l; move K26l before pvzI19; pose proof (proj2 pvzI19) as K26r; move K26r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K27l; move K27l before pvzI20; pose proof (proj2 pvzI20) as K27r; move K27r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K28l; move K28l before pvzI21; pose proof (proj2 pvzI21) as K28r; move K28r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 37%nat => vz_37 | 38%nat => vz_38 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbskW2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbskW2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbskW2.kn0).
  { unfold know_ok, PbskW2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K5]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K7l K7r K9 K12; lia | clear - HV10l HV10r K7l K7r K9 K12; lia | clear - HV10l HV10r K7l K7r K9 K12; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K7l K7r K9 K12; lia | clear - HV10l HV10r K7l K7r K9 K12; lia | clear - HV10l HV10r K7l K7r K9 K12; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | evalEk ZA ltac:(clear - HV33l HV33r K17l K17r K20l K20r) | clear - HV10l HV10r K7l K7r K9 K12; lia | clear - HV10l HV10r K7l K7r K9 K12; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | evalEk ZA ltac:(clear - HV33l HV33r K17l K17r K20l K20r HV34l HV34r K16l K16r K18l K18r K26l K26r) | clear - HV10l HV10r K7l K7r K9 K12; lia | clear - HV10l HV10r K7l K7r K9 K12; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | evalEk ZA ltac:(clear - HV33l HV33r K17l K17r K20l K20r HV35l HV35r K19l K19r) | clear - HV10l HV10r K7l K7r K9 K12; lia | clear - HV10l HV10r K7l K7r K9 K12; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26l K26r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K17l K17r K20l K20r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26l K26r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K19l K19r K20l K20r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K17l K17r K20l K20r HV35l HV35r K19l K19r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV37l HV37r K25l K25r K26l K26r K27l K27r) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26l K26r HV37l HV37r K25l K25r K27l K27r) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26l K26r HV37l HV37r K25l K25r K27l K27r) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV37l HV37r K25l K25r K26l K26r K27l K27r HV38l HV38r K28l K28r) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K25l K25r K26l K26r K27l K27r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26l K26r HV37l HV37r K25l K25r K27l K27r) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K25l K25r K26l K26r K27l K27r HV38l HV38r K28l K28r) | exact (conj K27l K27r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K27l K27r K28l K28r) | exact (conj K28l K28r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbskW2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbskW2.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbskW2.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbskW2.ps0) with 0x78e40 in Hms. change (SR.ps_regs PbskW2.ps0) with (map (fun i => (i, nth i PbskW2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbskW2.ps0) with PbskW2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbskW2.regs0 PbskW2.regs_out0 60 KS_bskW2 KS_bskW2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbskW2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbskW2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskW2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbskW2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskW2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbskW2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskW2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbskW2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskW2.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbskW2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskW2.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbskW2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskW2.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbskW2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskW2.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbskW2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskW2.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbskW2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskW2.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbskW2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskW2.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbskW2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskW2.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbskW2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbskW2.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbskW2.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PbskW2z := BndP_Eb_050S9.LibSegEb_bskW2z.
Definition KS_bskW2z : list nat := Eval vm_compute in (BG.kept_list 60 PbskW2z.regs0 PbskW2z.regs_out0).
Lemma KS_bskW2z_ok : BG.kept_ok 60 PbskW2z.regs0 PbskW2z.regs_out0 KS_bskW2z = true. Proof. vm_compute. reflexivity. Qed.
Lemma bskW2z_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 208) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 120) -> getr R (reg 9) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 -> 6930432 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 10%nat) 24 ->
  (((V 2%nat) - 256) + 256 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 256)) -> L5.u64_at RSEGS M (V 10%nat) 0 -> L5.u64_at RSEGS M ((V 10%nat) + 8) 0 -> L5.u64_at RSEGS M ((V 10%nat) + 16) 0 ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 112) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) ((V 37%nat) + 1) -> L5.u64_at RSEGS M ((V 2%nat) - 96) ((V 37%nat) + 1) ->
  4096 <= (V 37%nat) <= 140737488355327 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1844 M) (st fx' R' 0x78e40 M')
        /\ (forall x, In x KS_bskW2z -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 727228
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 10%nat) + 8)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 2%nat) - 112)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 ((((V 10%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 23) = Z_to_bv 64 ((((V 2%nat) - 112) / 8) + 2147450880)
        /\ getr R' (reg 24) = Z_to_bv 64 (((V 10%nat) / 8) + 2147450880)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G10 G11 G12 G21 K0 K1 K2 pvzI7 K4 K5 K6 pvzI8 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 pvzI9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV55l; move HV55l before pvzI4; pose proof (proj2 pvzI4) as HV55r; move HV55r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV56l; move HV56l before pvzI5; pose proof (proj2 pvzI5) as HV56r; move HV56r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV57l; move HV57l before pvzI6; pose proof (proj2 pvzI6) as HV57r; move HV57r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K7l; move K7l before pvzI8; pose proof (proj2 pvzI8) as K7r; move K7r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K20l; move K20l before pvzI9; pose proof (proj2 pvzI9) as K20r; move K20r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 37%nat => Z_to_bv 64 vz_37 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 37%nat => vz_37 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbskW2z.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbskW2z.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbskW2z.kn0).
  { unfold know_ok, PbskW2z.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K5]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K7l K7r K9 K12; lia | clear - HV10l HV10r K7l K7r K9 K12; lia | clear - HV10l HV10r K7l K7r K9 K12; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K7l K7r K9 K12; lia | clear - HV10l HV10r K7l K7r K9 K12; lia | clear - HV10l HV10r K7l K7r K9 K12; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K7l K7r K9 K12; lia | clear - HV10l HV10r K7l K7r K9 K12; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K7l K7r K9 K12; lia | clear - HV10l HV10r K7l K7r K9 K12; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K7l K7r K9 K12; lia | clear - HV10l HV10r K7l K7r K9 K12; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbskW2z.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbskW2z.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbskW2z.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbskW2z.ps0) with 0x78e40 in Hms. change (SR.ps_regs PbskW2z.ps0) with (map (fun i => (i, nth i PbskW2z.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbskW2z.ps0) with PbskW2z.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbskW2z.regs0 PbskW2z.regs_out0 60 KS_bskW2z KS_bskW2z_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbskW2z.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbskW2z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskW2z.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbskW2z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskW2z.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbskW2z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskW2z.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbskW2z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskW2z.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbskW2z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskW2z.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbskW2z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskW2z.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbskW2z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskW2z.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbskW2z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskW2z.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbskW2z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskW2z.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbskW2z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskW2z.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbskW2z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskW2z.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbskW2z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbskW2z.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbskW2z.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PbskW3 := BndP_Eb_050S9.LibSegEb_bskW3.
Definition KS_bskW3 : list nat := Eval vm_compute in (BG.kept_list 60 PbskW3.regs0 PbskW3.regs_out0).
Lemma KS_bskW3_ok : BG.kept_ok 60 PbskW3.regs0 PbskW3.regs_out0 KS_bskW3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bskW3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 208) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 120) -> getr R (reg 9) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 19) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 20) = Z_to_bv 64 (V 37%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 ((((V 10%nat) + 8) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 ((((V 2%nat) - 112) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (((V 10%nat) / 8) + 2147450880) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 -> 6930432 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 10%nat) 24 ->
  (((V 2%nat) - 256) + 256 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 256)) -> L5.u64_at RSEGS M (V 10%nat) (V 33%nat) -> L5.u64_at RSEGS M ((V 10%nat) + 8) ((V 33%nat) + (V 34%nat)) -> L5.u64_at RSEGS M ((V 10%nat) + 16) ((V 33%nat) + (V 35%nat)) ->
  0 <= (V 33%nat) <= 140737488355328 -> 0 <= (V 34%nat) <= 17179869184 -> 0 <= (V 35%nat) <= 17179869184 -> 0 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 34%nat) + (V 37%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (((V 34%nat) + (V 37%nat)) + 1) -> L5.u64_at RSEGS M ((V 2%nat) - 96) ((V 37%nat) + (V 38%nat)) ->
  4096 <= (V 37%nat) <= 140737488355328 -> 4096 <= ((V 34%nat) + (V 37%nat)) <= 140737488355327 -> 4096 <= ((V 37%nat) + (V 38%nat)) <= 140737488355328 -> 1 <= (V 38%nat) <= 17179869184 ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) 726172 -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 39%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 43%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 168) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 176) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 184) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 53%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 200) (V 54%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 208) (V 58%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 120) <= bv_unsigned a < ((V 2%nat) - 120) + 32) -> ~ (((V 10%nat) + 0) <= bv_unsigned a < ((V 10%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 120) <= i < ((V 2%nat) - 120) + 32) -> ~ (((V 10%nat) + 0) <= i < ((V 10%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb18bc M) (st fx' R' 0xb1b20 M')
        /\ (forall x, In x KS_bskW3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 726172
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 39%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 10%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 34%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 53%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 54%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 58%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) ((V 33%nat) + (V 35%nat))
        /\ L5.u64_at RSEGS M' ((V 10%nat) + 16) ((V 37%nat) + (V 38%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 10%nat) + 8) (((V 34%nat) + (V 37%nat)) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 33%nat)
        /\ L5.u64_at RSEGS M' (V 10%nat) (V 37%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G22 G23 G24 K0 K1 K2 pvzI20 K4 K5 K6 pvzI21 K8 K9 K10 K11 K12 K13 K14 K15 pvzI22 pvzI23 pvzI24 pvzI25 K20 K21 K22 K23 pvzI26 pvzI27 pvzI28 pvzI29 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV35l; move HV35l before pvzI5; pose proof (proj2 pvzI5) as HV35r; move HV35r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV37l; move HV37l before pvzI6; pose proof (proj2 pvzI6) as HV37r; move HV37r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV38l; move HV38l before pvzI7; pose proof (proj2 pvzI7) as HV38r; move HV38r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV39l; move HV39l before pvzI8; pose proof (proj2 pvzI8) as HV39r; move HV39r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV42l; move HV42l before pvzI9; pose proof (proj2 pvzI9) as HV42r; move HV42r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV43l; move HV43l before pvzI10; pose proof (proj2 pvzI10) as HV43r; move HV43r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV48l; move HV48l before pvzI11; pose proof (proj2 pvzI11) as HV48r; move HV48r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV49l; move HV49l before pvzI12; pose proof (proj2 pvzI12) as HV49r; move HV49r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV52l; move HV52l before pvzI13; pose proof (proj2 pvzI13) as HV52r; move HV52r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV53l; move HV53l before pvzI14; pose proof (proj2 pvzI14) as HV53r; move HV53r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV54l; move HV54l before pvzI15; pose proof (proj2 pvzI15) as HV54r; move HV54r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV55l; move HV55l before pvzI16; pose proof (proj2 pvzI16) as HV55r; move HV55r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV56l; move HV56l before pvzI17; pose proof (proj2 pvzI17) as HV56r; move HV56r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV57l; move HV57l before pvzI18; pose proof (proj2 pvzI18) as HV57r; move HV57r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV58l; move HV58l before pvzI19; pose proof (proj2 pvzI19) as HV58r; move HV58r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K3l; move K3l before pvzI20; pose proof (proj2 pvzI20) as K3r; move K3r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K7l; move K7l before pvzI21; pose proof (proj2 pvzI21) as K7r; move K7r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K16l; move K16l before pvzI22; pose proof (proj2 pvzI22) as K16r; move K16r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K17l; move K17l before pvzI23; pose proof (proj2 pvzI23) as K17r; move K17r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K18l; move K18l before pvzI24; pose proof (proj2 pvzI24) as K18r; move K18r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K19l; move K19l before pvzI25; pose proof (proj2 pvzI25) as K19r; move K19r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K24l; move K24l before pvzI26; pose proof (proj2 pvzI26) as K24r; move K24r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as K25l; move K25l before pvzI27; pose proof (proj2 pvzI27) as K25r; move K25r before pvzI27; clear pvzI27. pose proof (proj1 pvzI28) as K26l; move K26l before pvzI28; pose proof (proj2 pvzI28) as K26r; move K26r before pvzI28; clear pvzI28. pose proof (proj1 pvzI29) as K27l; move K27l before pvzI29; pose proof (proj2 pvzI29) as K27r; move K27r before pvzI29; clear pvzI29.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *. set (vz_54 := V 54%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | 54%nat => Z_to_bv 64 vz_54 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 42%nat => vz_42 | 43%nat => vz_43 | 48%nat => vz_48 | 49%nat => vz_49 | 52%nat => vz_52 | 53%nat => vz_53 | 54%nat => vz_54 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 58%nat => vz_58 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 59%nat. }
  assert (HR: regs_ok E PbskW3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbskW3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbskW3.kn0).
  { unfold know_ok, PbskW3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K5]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K7l K7r K9 K12; lia | clear - HV10l HV10r K7l K7r K9 K12; lia | clear - HV10l HV10r K7l K7r K9 K12; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K7l K7r K9 K12; lia | clear - HV10l HV10r K7l K7r K9 K12; lia | clear - HV10l HV10r K7l K7r K9 K12; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | evalEk ZA ltac:(clear - HV33l HV33r K16l K16r K19l K19r) | clear - HV10l HV10r K7l K7r K9 K12; lia | clear - HV10l HV10r K7l K7r K9 K12; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | evalEk ZA ltac:(clear - HV33l HV33r K16l K16r K19l K19r HV34l HV34r K17l K17r K25l K25r) | clear - HV10l HV10r K7l K7r K9 K12; lia | clear - HV10l HV10r K7l K7r K9 K12; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | evalEk ZA ltac:(clear - HV33l HV33r K16l K16r K19l K19r HV35l HV35r K18l K18r) | clear - HV10l HV10r K7l K7r K9 K12; lia | clear - HV10l HV10r K7l K7r K9 K12; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K16l K16r K19l K19r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K17l K17r K25l K25r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K18l K18r K19l K19r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K16l K16r K19l K19r HV35l HV35r K18l K18r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV37l HV37r K24l K24r K25l K25r K26l K26r) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV34l HV34r K17l K17r K25l K25r HV37l HV37r K24l K24r K26l K26r) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV34l HV34r K17l K17r K25l K25r HV37l HV37r K24l K24r K26l K26r) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV37l HV37r K24l K24r K25l K25r K26l K26r HV38l HV38r K27l K27r) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K24l K24r K25l K25r K26l K26r) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K17l K17r K25l K25r HV37l HV37r K24l K24r K26l K26r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K24l K24r K25l K25r K26l K26r HV38l HV38r K27l K27r) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K26l K26r K27l K27r) | exact (conj K27l K27r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV39l HV39r) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV54l HV54r) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV58l HV58r) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K37]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbskW3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbskW3.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 120) <= bv_unsigned a < (vz_2 - 120) + 32) -> ~ ((vz_10 + 0) <= bv_unsigned a < (vz_10 + 0) + 24) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PbskW3.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K12 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV10l HV10r K7l K7r K9 K12) | evalEk' ZA Hag ltac:(clear) | clear - HV10l HV10r K7l K7r K9 K12 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbskW3.ps0) with 0xb1b20 in Hms. change (SR.ps_regs PbskW3.ps0) with (map (fun i => (i, nth i PbskW3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbskW3.ps0) with PbskW3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbskW3.regs0 PbskW3.regs_out0 60 KS_bskW3 KS_bskW3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbskW3.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbskW3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskW3.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbskW3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskW3.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbskW3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskW3.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbskW3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskW3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbskW3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskW3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbskW3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskW3.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbskW3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskW3.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbskW3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskW3.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbskW3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskW3.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbskW3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskW3.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbskW3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskW3.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbskW3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskW3.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbskW3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskW3.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbskW3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K16l K16r K19l K19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K16l K16r K19l K19r HV35l HV35r K18l K18r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K7l K7r K9 K12) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K24l K24r K25l K25r K26l K26r HV38l HV38r K27l K27r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K16l K16r K19l K19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K7l K7r K9 K12) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K17l K17r K25l K25r HV37l HV37r K24l K24r K26l K26r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K16l K16r K19l K19r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K7l K7r K9 K12) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K24l K24r K25l K25r K26l K26r) | clear; lia].
Qed.

Module PbskS3n := BndP_Eb_049S9.LibSegEb_bskS3n.
Definition KS_bskS3n : list nat := Eval vm_compute in (BG.kept_list 60 PbskS3n.regs0 PbskS3n.regs_out0).
Lemma KS_bskS3n_ok : BG.kept_ok 60 PbskS3n.regs0 PbskS3n.regs_out0 KS_bskS3n = true. Proof. vm_compute. reflexivity. Qed.
Lemma bskS3n_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 9) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 ((((V 10%nat) + 8) / 8) + 2147450880) -> getr R (reg 20) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 -> 6930432 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 10%nat) 24 ->
  (((V 2%nat) - 256) + 256 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 256)) -> L5.u64_at RSEGS M ((V 10%nat) + 8) ((V 37%nat) + 1) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 112) 0 ->
  L5.u64_at RSEGS M ((V 2%nat) - 104) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 96) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 10%nat) -> 4096 <= (V 37%nat) <= 140737488355327 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 144) <= bv_unsigned a < ((V 2%nat) - 144) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 144) <= i < ((V 2%nat) - 144) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb149c M) (st fx' R' 0xb1acc M')
        /\ (forall x, In x KS_bskS3n -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 726192
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 37%nat) + 1)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 88)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 2147450880
        /\ getr R' (reg 14) = Z_to_bv 64 (((V 2%nat) - 88) / 8)
        /\ getr R' (reg 15) = Z_to_bv 64 ((((V 2%nat) - 104) / 8) + 2147450880)
        /\ getr R' (reg 16) = Z_to_bv 64 0
        /\ getr R' (reg 17) = Z_to_bv 64 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G11 G12 G18 G19 G20 K0 K1 K2 pvzI8 K4 K5 K6 pvzI9 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 pvzI10.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV55l; move HV55l before pvzI5; pose proof (proj2 pvzI5) as HV55r; move HV55r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV56l; move HV56l before pvzI6; pose proof (proj2 pvzI6) as HV56r; move HV56r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV57l; move HV57l before pvzI7; pose proof (proj2 pvzI7) as HV57r; move HV57r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K7l; move K7l before pvzI9; pose proof (proj2 pvzI9) as K7r; move K7r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K19l; move K19l before pvzI10; pose proof (proj2 pvzI10) as K19r; move K19r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 36%nat => vz_36 | 37%nat => vz_37 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbskS3n.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbskS3n.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbskS3n.kn0).
  { unfold know_ok, PbskS3n.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K5]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K7l K7r K9 K12; lia | clear - HV10l HV10r K7l K7r K9 K12; lia | clear - HV10l HV10r K7l K7r K9 K12; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K7l K7r K9 K12; lia | clear - HV10l HV10r K7l K7r K9 K12; lia | clear - HV10l HV10r K7l K7r K9 K12; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | evalEk ZA ltac:(clear - HV37l HV37r K19l K19r) | clear - HV10l HV10r K7l K7r K9 K12; lia | clear - HV10l HV10r K7l K7r K9 K12; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbskS3n.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbskS3n.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 144) <= bv_unsigned a < (vz_2 - 144) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbskS3n.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K12 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbskS3n.ps0) with 0xb1acc in Hms. change (SR.ps_regs PbskS3n.ps0) with (map (fun i => (i, nth i PbskS3n.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbskS3n.ps0) with PbskS3n.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbskS3n.regs0 PbskS3n.regs_out0 60 KS_bskS3n KS_bskS3n_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbskS3n.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbskS3n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS3n.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbskS3n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS3n.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbskS3n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS3n.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbskS3n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS3n.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbskS3n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS3n.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbskS3n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS3n.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbskS3n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS3n.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbskS3n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS3n.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PbskS3n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbskS3n.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PbskS3n.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PbskS3 := BndP_Eb_049S9.LibSegEb_bskS3.
Definition KS_bskS3 : list nat := Eval vm_compute in (BG.kept_list 60 PbskS3.regs0 PbskS3.regs_out0).
Lemma KS_bskS3_ok : BG.kept_ok 60 PbskS3.regs0 PbskS3.regs_out0 KS_bskS3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bskS3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 9) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 ((((V 10%nat) + 8) / 8) + 2147450880) -> getr R (reg 20) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 -> 6930432 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 10%nat) 24 ->
  (((V 2%nat) - 256) + 256 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 256)) -> L5.u64_at RSEGS M ((V 10%nat) + 8) (((V 34%nat) + (V 37%nat)) + 1) -> L5.u64_at RSEGS M ((V 2%nat) - 120) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 112) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 104) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) ((V 33%nat) + (V 35%nat)) -> 4096 <= (V 33%nat) <= 140737488355328 -> aligned (V 33%nat) 16 ->
  0 <= (V 34%nat) <= 17179869184 -> 1 <= (V 35%nat) <= 17179869184 -> 4096 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + (V 35%nat) <= 2147446784) ->
  (65536 + 6864896 <= (V 33%nat) \/ (V 33%nat) + (V 35%nat) <= 65536) -> 4096 <= (V 37%nat) <= 140737488355328 -> 4096 <= ((V 34%nat) + (V 37%nat)) <= 140737488355327 -> 4096 <= ((V 37%nat) + (V 38%nat)) <= 140737488355328 ->
  1 <= (V 38%nat) <= 17179869184 -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 10%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 144) <= bv_unsigned a < ((V 2%nat) - 144) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 144) <= i < ((V 2%nat) - 144) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb149c M) (st fx' R' 0xd9208 M')
        /\ (forall x, In x KS_bskS3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 726192
        /\ getr R' (reg 8) = Z_to_bv 64 (((V 34%nat) + (V 37%nat)) + 1)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 2147450880
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 15) = Z_to_bv 64 ((((V 2%nat) - 104) / 8) + 2147450880)
        /\ getr R' (reg 16) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 17) = Z_to_bv 64 (V 33%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 G2 G8 G9 G10 G11 G12 G18 G19 G20 K0 K1 K2 pvzI12 K4 K5 K6 pvzI13 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 pvzI14 K19 pvzI15 pvzI16 pvzI17 K23 K24 pvzI18 pvzI19 pvzI20 pvzI21 K29.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV35l; move HV35l before pvzI5; pose proof (proj2 pvzI5) as HV35r; move HV35r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV36l; move HV36l before pvzI6; pose proof (proj2 pvzI6) as HV36r; move HV36r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV37l; move HV37l before pvzI7; pose proof (proj2 pvzI7) as HV37r; move HV37r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV38l; move HV38l before pvzI8; pose proof (proj2 pvzI8) as HV38r; move HV38r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV55l; move HV55l before pvzI9; pose proof (proj2 pvzI9) as HV55r; move HV55r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV56l; move HV56l before pvzI10; pose proof (proj2 pvzI10) as HV56r; move HV56r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV57l; move HV57l before pvzI11; pose proof (proj2 pvzI11) as HV57r; move HV57r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K3l; move K3l before pvzI12; pose proof (proj2 pvzI12) as K3r; move K3r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K7l; move K7l before pvzI13; pose proof (proj2 pvzI13) as K7r; move K7r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K18l; move K18l before pvzI14; pose proof (proj2 pvzI14) as K18r; move K18r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K20l; move K20l before pvzI15; pose proof (proj2 pvzI15) as K20r; move K20r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K21l; move K21l before pvzI16; pose proof (proj2 pvzI16) as K21r; move K21r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K22l; move K22l before pvzI17; pose proof (proj2 pvzI17) as K22r; move K22r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K25l; move K25l before pvzI18; pose proof (proj2 pvzI18) as K25r; move K25r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K26l; move K26l before pvzI19; pose proof (proj2 pvzI19) as K26r; move K26r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K27l; move K27l before pvzI20; pose proof (proj2 pvzI20) as K27r; move K27r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K28l; move K28l before pvzI21; pose proof (proj2 pvzI21) as K28r; move K28r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbskS3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbskS3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbskS3.kn0).
  { unfold know_ok, PbskS3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K5]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K7l K7r K9 K12; lia | clear - HV10l HV10r K7l K7r K9 K12; lia | clear - HV10l HV10r K7l K7r K9 K12; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K7l K7r K9 K12; lia | clear - HV10l HV10r K7l K7r K9 K12; lia | clear - HV10l HV10r K7l K7r K9 K12; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | evalEk ZA ltac:(clear - HV34l HV34r K20l K20r K26l K26r HV37l HV37r K25l K25r K27l K27r) | clear - HV10l HV10r K7l K7r K9 K12; lia | clear - HV10l HV10r K7l K7r K9 K12; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV33l HV33r K18l K18r K22l K22r K23 K24) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV33l HV33r K18l K18r K22l K22r K23 K24) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV33l HV33r K18l K18r K22l K22r K23 K24) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV33l HV33r K18l K18r K22l K22r K23 K24 HV35l HV35r K21l K21r) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K18l K18r K22l K22r K23 K24) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K18l K18r K22l K22r K23 K24) | clear; lia | exact K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K20l K20r K26l K26r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K21l K21r K22l K22r K23 K24) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K18l K18r K22l K22r K23 K24 HV35l HV35r K21l K21r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K18l K18r K22l K22r K23 K24) | evalEk ZA ltac:(clear - HV35l HV35r K21l K21r K22l K22r K23 K24) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K18l K18r K22l K22r K23 K24) | evalEk ZA ltac:(clear - HV35l HV35r K21l K21r K22l K22r K23 K24) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K25l K25r K26l K26r K27l K27r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K20l K20r K26l K26r HV37l HV37r K25l K25r K27l K27r) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K25l K25r K26l K26r K27l K27r HV38l HV38r K28l K28r) | exact (conj K27l K27r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K27l K27r K28l K28r) | exact (conj K28l K28r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K29]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbskS3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbskS3.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 144) <= bv_unsigned a < (vz_2 - 144) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbskS3.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K12 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbskS3.ps0) with 0xd9208 in Hms. change (SR.ps_regs PbskS3.ps0) with (map (fun i => (i, nth i PbskS3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbskS3.ps0) with PbskS3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbskS3.regs0 PbskS3.regs_out0 60 KS_bskS3 KS_bskS3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbskS3.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbskS3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS3.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbskS3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbskS3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbskS3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS3.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbskS3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS3.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbskS3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS3.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbskS3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS3.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbskS3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS3.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PbskS3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbskS3.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PbskS3.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PbskS4 := BndP_Eb_049S9.LibSegEb_bskS4.
Definition KS_bskS4 : list nat := Eval vm_compute in (BG.kept_list 60 PbskS4.regs0 PbskS4.regs_out0).
Lemma KS_bskS4_ok : BG.kept_ok 60 PbskS4.regs0 PbskS4.regs_out0 KS_bskS4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bskS4_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 41%nat) -> getr R (reg 9) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 ((((V 10%nat) + 8) / 8) + 2147450880) -> getr R (reg 20) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 -> 6930432 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 10%nat) 24 ->
  (((V 2%nat) - 256) + 256 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 256)) -> L5.u64_at RSEGS M ((V 2%nat) - 40) 725624 -> L5.u64_at RSEGS M ((V 2%nat) - 48) ((V 10%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 56) ((((V 10%nat) + 8) / 8) + 2147450880) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) ((V 33%nat) + (V 34%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 51%nat) -> 0 <= (V 33%nat) <= 140737488355328 ->
  0 <= (V 34%nat) <= 17179869184 -> 0 <= (V 35%nat) <= 17179869184 -> 0 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 41%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb14b0 M) (st fx' R' 0xb14d0 M')
        /\ (forall x, In x KS_bskS4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 725624
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 32)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 10%nat) + 8)
        /\ getr R' (reg 9) = Z_to_bv 64 ((((V 10%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 33%nat) + (V 34%nat))
        /\ getr R' (reg 19) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 51%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 G2 G8 G9 G10 G11 G12 G18 G19 G20 K0 K1 K2 pvzI13 K4 K5 K6 pvzI14 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV35l; move HV35l before pvzI5; pose proof (proj2 pvzI5) as HV35r; move HV35r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV36l; move HV36l before pvzI6; pose proof (proj2 pvzI6) as HV36r; move HV36r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV41l; move HV41l before pvzI7; pose proof (proj2 pvzI7) as HV41r; move HV41r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV50l; move HV50l before pvzI8; pose proof (proj2 pvzI8) as HV50r; move HV50r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV51l; move HV51l before pvzI9; pose proof (proj2 pvzI9) as HV51r; move HV51r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV55l; move HV55l before pvzI10; pose proof (proj2 pvzI10) as HV55r; move HV55r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV56l; move HV56l before pvzI11; pose proof (proj2 pvzI11) as HV56r; move HV56r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV57l; move HV57l before pvzI12; pose proof (proj2 pvzI12) as HV57r; move HV57r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K3l; move K3l before pvzI13; pose proof (proj2 pvzI13) as K3r; move K3r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K7l; move K7l before pvzI14; pose proof (proj2 pvzI14) as K7r; move K7r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K19l; move K19l before pvzI15; pose proof (proj2 pvzI15) as K19r; move K19r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K20l; move K20l before pvzI16; pose proof (proj2 pvzI16) as K20r; move K20r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K21l; move K21l before pvzI17; pose proof (proj2 pvzI17) as K21r; move K21r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K22l; move K22l before pvzI18; pose proof (proj2 pvzI18) as K22r; move K22r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K23l; move K23l before pvzI19; pose proof (proj2 pvzI19) as K23r; move K23r before pvzI19; clear pvzI19.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 41%nat => Z_to_bv 64 vz_41 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 41%nat => vz_41 | 50%nat => vz_50 | 51%nat => vz_51 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbskS4.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbskS4.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbskS4.kn0).
  { unfold know_ok, PbskS4.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K5]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K7l K7r K9 K12; lia | clear - HV10l HV10r K7l K7r K9 K12; lia | clear - HV10l HV10r K7l K7r K9 K12; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K7l K7r K9 K12; lia | clear - HV10l HV10r K7l K7r K9 K12; lia | clear - HV10l HV10r K7l K7r K9 K12; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K22l K22r HV34l HV34r K20l K20r) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K22l K22r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K21l K21r K22l K22r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K22l K22r HV35l HV35r K21l K21r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbskS4.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbskS4.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbskS4.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbskS4.ps0) with 0xb14d0 in Hms. change (SR.ps_regs PbskS4.ps0) with (map (fun i => (i, nth i PbskS4.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbskS4.ps0) with PbskS4.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbskS4.regs0 PbskS4.regs_out0 60 KS_bskS4 KS_bskS4_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbskS4.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbskS4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS4.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbskS4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS4.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbskS4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS4.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbskS4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS4.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbskS4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS4.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbskS4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbskS4.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbskS4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbskS4.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbskS4.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

End PEBSKPP.
