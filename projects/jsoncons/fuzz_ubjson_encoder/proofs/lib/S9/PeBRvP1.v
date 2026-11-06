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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.seg Require BndP_Eb_042S9 BndP_Eb_045S9 BndP_Eb_044S9.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEBRVP1.
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

Module PbrvA := BndP_Eb_042S9.LibSegEb_brvA.
Definition KS_brvA : list nat := Eval vm_compute in (BG.kept_list 72 PbrvA.regs0 PbrvA.regs_out0).
Lemma KS_brvA_ok : BG.kept_ok 72 PbrvA.regs0 PbrvA.regs_out0 KS_brvA = true. Proof. vm_compute. reflexivity. Qed.
Lemma brvA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 (V 37%nat) -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 (V 38%nat) ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6930432 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 128)) -> 6930432 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 128) + 128 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 128)) ->
  ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb73bc M) (st fx' R' 0x5f0dc M')
        /\ (forall x, In x KS_brvA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 750648
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 10) = Z_to_bv 64 320
        /\ getr R' (reg 11) = Z_to_bv 64 1335544
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 20) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 2147450880
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G10 G11 G12 G13 K0 K1 K2 pvzI6 K4 K5 pvzI7 K7 K8 K9 K10 K11 K12 K13 pvzI8 K15 K16 K17 K18 K19 K20.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K6l; move K6l before pvzI7; pose proof (proj2 pvzI7) as K6r; move K6r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K14l; move K14l before pvzI8; pose proof (proj2 pvzI8) as K14r; move K14r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 39%nat. }
  assert (HR: regs_ok E PbrvA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbrvA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbrvA.kn0).
  { unfold know_ok, PbrvA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbrvA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbrvA.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 128) <= bv_unsigned a < (vz_2 - 128) + 128) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbrvA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbrvA.ps0) with 0x5f0dc in Hms. change (SR.ps_regs PbrvA.ps0) with (map (fun i => (i, nth i PbrvA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbrvA.ps0) with PbrvA.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbrvA.regs0 PbrvA.regs_out0 72 KS_brvA KS_brvA_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbrvA.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbrvA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvA.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbrvA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvA.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbrvA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvA.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbrvA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvA.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbrvA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvA.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbrvA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvA.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbrvA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvA.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbrvA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvA.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbrvA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvA.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbrvA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvA.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbrvA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvA.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PbrvA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
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

Module PbrvB := BndP_Eb_042S9.LibSegEb_brvB.
Definition KS_brvB : list nat := Eval vm_compute in (BG.kept_list 72 PbrvB.regs0 PbrvB.regs_out0).
Lemma KS_brvB_ok : BG.kept_ok 72 PbrvB.regs0 PbrvB.regs_out0 KS_brvB = true. Proof. vm_compute. reflexivity. Qed.
Lemma brvB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 (V 37%nat) -> getr R (reg 23) = Z_to_bv 64 (V 33%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6930432 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 128)) -> 6930432 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 128) + 128 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 128)) ->
  ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) -> 6930432 <= (V 47%nat) <= 140737488354816 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 512 ->
  L5.writable RSEGS M (V 47%nat) 512 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 64 -> L5KA.zeros_at M (((V 47%nat) / 8) + 2147450880) 64 ->
  L5.u64_at RSEGS M ((V 47%nat) + 504) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) ->
  ((V 47%nat) + 512 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 512 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) -> ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 512 <= (V 36%nat)) ->
  ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) -> ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 64 <= (((V 36%nat) / 8) + 2147450880)) -> ((V 38%nat) + 16 <= (V 47%nat) \/ (V 47%nat) + 512 <= (V 38%nat)) -> ((V 38%nat) + 16 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 38%nat)) ->
  ((((V 38%nat) / 8) + 2147450880) + 2 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 64 <= (((V 38%nat) / 8) + 2147450880)) -> ((V 47%nat) + 512 <= 65536 \/ 65536 + 1241088 <= (V 47%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 112) <= bv_unsigned a < ((V 2%nat) - 112) + 8) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 40) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 112) <= i < ((V 2%nat) - 112) + 8) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 40) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb7438 M) (st fx' R' 0xb754c M')
        /\ (forall x, In x KS_brvB -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 18446744073709551602
        /\ getr R' (reg 11) = Z_to_bv 64 18446744073709551608
        /\ getr R' (reg 12) = Z_to_bv 64 99
        /\ getr R' (reg 13) = Z_to_bv 64 88144
        /\ getr R' (reg 14) = Z_to_bv 64 750524
        /\ getr R' (reg 18) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 47%nat)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450915) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450914) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450913) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450912) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450907) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450906) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450905) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450904) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450911) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450910) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450909) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450908) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450899) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450898) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450897) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450896) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450903) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450902) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450901) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450900) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450891) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450890) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450889) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450888) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450895) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450894) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450893) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450892) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450887) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450885) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450919) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450918) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450917) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450916) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450883) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450882) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450881) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450880) 241
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 16) 750524
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 8) 88144
        /\ L5.u64_at RSEGS M' (V 47%nat) 1102416563
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 47%nat)
        /\ L5.defined M' ((V 47%nat) + 24) 488
        /\ L5KA.zeros_at M' (((V 47%nat) / 8) + 2147450920) 24).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G20 G21 G22 G23 G27 K0 K1 K2 pvzI8 K4 K5 pvzI9 K7 K8 K9 K10 K11 K12 K13 pvzI10 K15 K16 K17 K18 K19 K20 pvzI11 K22 K23 K24 K25 K26 K27 K28 pvzI12 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV47l; move HV47l before pvzI6; pose proof (proj2 pvzI6) as HV47r; move HV47r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV48l; move HV48l before pvzI7; pose proof (proj2 pvzI7) as HV48r; move HV48r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K14l; move K14l before pvzI10; pose proof (proj2 pvzI10) as K14r; move K14r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K21l; move K21l before pvzI11; pose proof (proj2 pvzI11) as K21r; move K21r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K29l; move K29l before pvzI12; pose proof (proj2 pvzI12) as K29r; move K29r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PbrvB.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbrvB.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbrvB.kn0).
  { unfold know_ok, PbrvB.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | clear; lia | exact K22]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | exactA K26]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear - HV48l HV48r K29l K29r) | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K29l K29r) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K29l K29r; lia | clear - HV48l HV48r K29l K29r; lia | clear - HV48l HV48r K29l K29r; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K29l K29r) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K29l K29r) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K29l K29r) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K29l K29r) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K29l K29r) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K41; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbrvB.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbrvB.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 112) <= bv_unsigned a < (vz_2 - 112) + 8) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 24) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 40) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PbrvB.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K21l K21r Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K21l K21r Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbrvB.ps0) with 0xb754c in Hms. change (SR.ps_regs PbrvB.ps0) with (map (fun i => (i, nth i PbrvB.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbrvB.ps0) with PbrvB.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbrvB.regs0 PbrvB.regs_out0 72 KS_brvB KS_brvB_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbrvB.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbrvB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvB.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbrvB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvB.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbrvB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvB.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbrvB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvB.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbrvB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvB.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbrvB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvB.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbrvB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvB.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PbrvB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 23%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 24%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 25%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 26%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 27%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 28%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 29%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 30%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 31%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 32%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 33%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 34%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 35%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 36%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 37%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 38%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 39%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 40%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 41%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 42%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 43%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 44%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply zeros_of_KZeroa; [apply Hcells; apply (nth_error_In _ 45%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PbrvTN := BndP_Eb_045S9.LibSegEb_brvTN.
Definition KS_brvTN : list nat := Eval vm_compute in (BG.kept_list 72 PbrvTN.regs0 PbrvTN.regs_out0).
Lemma KS_brvTN_ok : BG.kept_ok 72 PbrvTN.regs0 PbrvTN.regs_out0 KS_brvTN = true. Proof. vm_compute. reflexivity. Qed.
Lemma brvTN_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 12) = Z_to_bv 64 99 -> getr R (reg 18) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 47%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 (V 37%nat) -> getr R (reg 23) = Z_to_bv 64 78 -> getr R (reg 26) = Z_to_bv 64 (V 47%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6930432 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 128)) -> 6930432 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 128) + 128 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 128)) ->
  ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb754c M) (st fx' R' 0xb7f40 M')
        /\ (forall x, In x KS_brvTN -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 753472
        /\ getr R' (reg 11) = Z_to_bv 64 143728).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G12 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI6 K4 K5 pvzI7 K7 K8 K9 K10 K11 K12 K13 pvzI8 K15 K16 K17 K18 K19 K20.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K6l; move K6l before pvzI7; pose proof (proj2 pvzI7) as K6r; move K6r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K14l; move K14l before pvzI8; pose proof (proj2 pvzI8) as K14r; move K14r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 48%nat. }
  assert (HR: regs_ok E PbrvTN.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbrvTN.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbrvTN.kn0).
  { unfold know_ok, PbrvTN.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbrvTN.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbrvTN.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbrvTN.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbrvTN.ps0) with 0xb7f40 in Hms. change (SR.ps_regs PbrvTN.ps0) with (map (fun i => (i, nth i PbrvTN.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbrvTN.ps0) with PbrvTN.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbrvTN.regs0 PbrvTN.regs_out0 72 KS_brvTN KS_brvTN_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbrvTN.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbrvTN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbrvTN.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbrvTN.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PbrvTZ := BndP_Eb_045S9.LibSegEb_brvTZ.
Definition KS_brvTZ : list nat := Eval vm_compute in (BG.kept_list 72 PbrvTZ.regs0 PbrvTZ.regs_out0).
Lemma KS_brvTZ_ok : BG.kept_ok 72 PbrvTZ.regs0 PbrvTZ.regs_out0 KS_brvTZ = true. Proof. vm_compute. reflexivity. Qed.
Lemma brvTZ_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 12) = Z_to_bv 64 99 -> getr R (reg 18) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 47%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 (V 37%nat) -> getr R (reg 23) = Z_to_bv 64 90 -> getr R (reg 26) = Z_to_bv 64 (V 47%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6930432 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 128)) -> 6930432 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 128) + 128 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 128)) ->
  ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) -> 6930432 <= (V 37%nat) <= 140737488355320 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 8 <= 2147446784) ->
  L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 1 -> L5.writable RSEGS M (V 37%nat) 8 -> (((V 2%nat) - 128) + 128 <= (V 37%nat) \/ (V 37%nat) + 8 <= ((V 2%nat) - 128)) -> L5.u64_at RSEGS M (V 37%nat) 1277312 ->
  L5KA.zeros_at M 2147610544 16 -> ((V 36%nat) + 384 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 36%nat)) -> ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 38%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb754c M) (st fx' R' 0xad588 M')
        /\ (forall x, In x KS_brvTZ -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 751868
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 710024).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G12 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI6 K4 K5 pvzI7 K7 K8 K9 K10 K11 K12 K13 pvzI8 K15 K16 K17 K18 K19 K20 pvzI9 K22 K23 K24 K25 K26 K27 K28 K29 K30.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K6l; move K6l before pvzI7; pose proof (proj2 pvzI7) as K6r; move K6r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K14l; move K14l before pvzI8; pose proof (proj2 pvzI8) as K14r; move K14r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K21l; move K21l before pvzI9; pose proof (proj2 pvzI9) as K21r; move K21r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 48%nat. }
  assert (HR: regs_ok E PbrvTZ.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbrvTZ.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbrvTZ.kn0).
  { unfold know_ok, PbrvTZ.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | clear; lia | exact K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K21l K21r; lia | clear - HV37l HV37r K21l K21r; lia | clear - HV37l HV37r K21l K21r; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K21l K21r; lia | clear - HV37l HV37r K21l K21r; lia | clear - HV37l HV37r K21l K21r; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K21l K21r; lia | clear - HV37l HV37r K21l K21r; lia | exactA K27]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbrvTZ.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbrvTZ.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbrvTZ.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbrvTZ.ps0) with 0xad588 in Hms. change (SR.ps_regs PbrvTZ.ps0) with (map (fun i => (i, nth i PbrvTZ.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbrvTZ.ps0) with PbrvTZ.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbrvTZ.regs0 PbrvTZ.regs_out0 72 KS_brvTZ KS_brvTZ_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbrvTZ.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbrvTZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTZ.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbrvTZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTZ.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbrvTZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTZ.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbrvTZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTZ.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbrvTZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbrvTZ.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbrvTZ.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PbrvTF := BndP_Eb_045S9.LibSegEb_brvTF.
Definition KS_brvTF : list nat := Eval vm_compute in (BG.kept_list 72 PbrvTF.regs0 PbrvTF.regs_out0).
Lemma KS_brvTF_ok : BG.kept_ok 72 PbrvTF.regs0 PbrvTF.regs_out0 KS_brvTF = true. Proof. vm_compute. reflexivity. Qed.
Lemma brvTF_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 12) = Z_to_bv 64 99 -> getr R (reg 18) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 47%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 (V 37%nat) -> getr R (reg 23) = Z_to_bv 64 70 -> getr R (reg 26) = Z_to_bv 64 (V 47%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6930432 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 128)) -> 6930432 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 128) + 128 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 128)) ->
  ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) -> 6930432 <= (V 37%nat) <= 140737488355320 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 8 <= 2147446784) ->
  L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 1 -> L5.writable RSEGS M (V 37%nat) 8 -> (((V 2%nat) - 128) + 128 <= (V 37%nat) \/ (V 37%nat) + 8 <= ((V 2%nat) - 128)) -> L5.u64_at RSEGS M (V 37%nat) 1277312 ->
  L5KA.zeros_at M 2147610544 16 -> ((V 36%nat) + 384 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 36%nat)) -> ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 38%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb754c M) (st fx' R' 0xad7ac M')
        /\ (forall x, In x KS_brvTF -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 751744
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 710572).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G12 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI6 K4 K5 pvzI7 K7 K8 K9 K10 K11 K12 K13 pvzI8 K15 K16 K17 K18 K19 K20 pvzI9 K22 K23 K24 K25 K26 K27 K28 K29 K30.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K6l; move K6l before pvzI7; pose proof (proj2 pvzI7) as K6r; move K6r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K14l; move K14l before pvzI8; pose proof (proj2 pvzI8) as K14r; move K14r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K21l; move K21l before pvzI9; pose proof (proj2 pvzI9) as K21r; move K21r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 48%nat. }
  assert (HR: regs_ok E PbrvTF.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbrvTF.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbrvTF.kn0).
  { unfold know_ok, PbrvTF.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | clear; lia | exact K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K21l K21r; lia | clear - HV37l HV37r K21l K21r; lia | clear - HV37l HV37r K21l K21r; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K21l K21r; lia | clear - HV37l HV37r K21l K21r; lia | clear - HV37l HV37r K21l K21r; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K21l K21r; lia | clear - HV37l HV37r K21l K21r; lia | exactA K27]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbrvTF.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbrvTF.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbrvTF.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbrvTF.ps0) with 0xad7ac in Hms. change (SR.ps_regs PbrvTF.ps0) with (map (fun i => (i, nth i PbrvTF.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbrvTF.ps0) with PbrvTF.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbrvTF.regs0 PbrvTF.regs_out0 72 KS_brvTF KS_brvTF_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbrvTF.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbrvTF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTF.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbrvTF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTF.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbrvTF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTF.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbrvTF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTF.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbrvTF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTF.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbrvTF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbrvTF.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbrvTF.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PbrvTT := BndP_Eb_045S9.LibSegEb_brvTT.
Definition KS_brvTT : list nat := Eval vm_compute in (BG.kept_list 72 PbrvTT.regs0 PbrvTT.regs_out0).
Lemma KS_brvTT_ok : BG.kept_ok 72 PbrvTT.regs0 PbrvTT.regs_out0 KS_brvTT = true. Proof. vm_compute. reflexivity. Qed.
Lemma brvTT_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 12) = Z_to_bv 64 99 -> getr R (reg 18) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 47%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 (V 37%nat) -> getr R (reg 23) = Z_to_bv 64 84 -> getr R (reg 26) = Z_to_bv 64 (V 47%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6930432 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 128)) -> 6930432 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 128) + 128 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 128)) ->
  ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) -> 6930432 <= (V 37%nat) <= 140737488355320 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 8 <= 2147446784) ->
  L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 1 -> L5.writable RSEGS M (V 37%nat) 8 -> (((V 2%nat) - 128) + 128 <= (V 37%nat) \/ (V 37%nat) + 8 <= ((V 2%nat) - 128)) -> L5.u64_at RSEGS M (V 37%nat) 1277312 ->
  L5KA.zeros_at M 2147610544 16 -> ((V 36%nat) + 384 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 36%nat)) -> ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 38%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb754c M) (st fx' R' 0xad7ac M')
        /\ (forall x, In x KS_brvTT -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 752004
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 710572
        /\ getr R' (reg 23) = Z_to_bv 64 1).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G12 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI6 K4 K5 pvzI7 K7 K8 K9 K10 K11 K12 K13 pvzI8 K15 K16 K17 K18 K19 K20 pvzI9 K22 K23 K24 K25 K26 K27 K28 K29 K30.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K6l; move K6l before pvzI7; pose proof (proj2 pvzI7) as K6r; move K6r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K14l; move K14l before pvzI8; pose proof (proj2 pvzI8) as K14r; move K14r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K21l; move K21l before pvzI9; pose proof (proj2 pvzI9) as K21r; move K21r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 48%nat. }
  assert (HR: regs_ok E PbrvTT.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbrvTT.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbrvTT.kn0).
  { unfold know_ok, PbrvTT.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | clear; lia | exact K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K21l K21r; lia | clear - HV37l HV37r K21l K21r; lia | clear - HV37l HV37r K21l K21r; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K21l K21r; lia | clear - HV37l HV37r K21l K21r; lia | clear - HV37l HV37r K21l K21r; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K21l K21r; lia | clear - HV37l HV37r K21l K21r; lia | exactA K27]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbrvTT.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbrvTT.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbrvTT.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbrvTT.ps0) with 0xad7ac in Hms. change (SR.ps_regs PbrvTT.ps0) with (map (fun i => (i, nth i PbrvTT.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbrvTT.ps0) with PbrvTT.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbrvTT.regs0 PbrvTT.regs_out0 72 KS_brvTT KS_brvTT_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbrvTT.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbrvTT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTT.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbrvTT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTT.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbrvTT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTT.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbrvTT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTT.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbrvTT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTT.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbrvTT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTT.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbrvTT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbrvTT.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbrvTT.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PbrvTA := BndP_Eb_044S9.LibSegEb_brvTA.
Definition KS_brvTA : list nat := Eval vm_compute in (BG.kept_list 72 PbrvTA.regs0 PbrvTA.regs_out0).
Lemma KS_brvTA_ok : BG.kept_ok 72 PbrvTA.regs0 PbrvTA.regs_out0 KS_brvTA = true. Proof. vm_compute. reflexivity. Qed.
Lemma brvTA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 12) = Z_to_bv 64 99 -> getr R (reg 18) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 47%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 (V 37%nat) -> getr R (reg 23) = Z_to_bv 64 91 -> getr R (reg 26) = Z_to_bv 64 (V 47%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6930432 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 128)) -> 6930432 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 128) + 128 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 128)) ->
  ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb754c M) (st fx' R' 0xbab88 M')
        /\ (forall x, In x KS_brvTA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 752552
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 38%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G12 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI6 K4 K5 pvzI7 K7 K8 K9 K10 K11 K12 K13 pvzI8 K15 K16 K17 K18 K19 K20.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K6l; move K6l before pvzI7; pose proof (proj2 pvzI7) as K6r; move K6r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K14l; move K14l before pvzI8; pose proof (proj2 pvzI8) as K14r; move K14r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 48%nat. }
  assert (HR: regs_ok E PbrvTA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbrvTA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbrvTA.kn0).
  { unfold know_ok, PbrvTA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbrvTA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbrvTA.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbrvTA.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbrvTA.ps0) with 0xbab88 in Hms. change (SR.ps_regs PbrvTA.ps0) with (map (fun i => (i, nth i PbrvTA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbrvTA.ps0) with PbrvTA.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbrvTA.regs0 PbrvTA.regs_out0 72 KS_brvTA KS_brvTA_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbrvTA.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbrvTA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTA.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbrvTA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTA.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbrvTA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbrvTA.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbrvTA.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PbrvTO := BndP_Eb_045S9.LibSegEb_brvTO.
Definition KS_brvTO : list nat := Eval vm_compute in (BG.kept_list 72 PbrvTO.regs0 PbrvTO.regs_out0).
Lemma KS_brvTO_ok : BG.kept_ok 72 PbrvTO.regs0 PbrvTO.regs_out0 KS_brvTO = true. Proof. vm_compute. reflexivity. Qed.
Lemma brvTO_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 12) = Z_to_bv 64 99 -> getr R (reg 18) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 47%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 (V 37%nat) -> getr R (reg 23) = Z_to_bv 64 123 -> getr R (reg 26) = Z_to_bv 64 (V 47%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6930432 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 128)) -> 6930432 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 128) + 128 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 128)) ->
  ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb754c M) (st fx' R' 0xbb3f0 M')
        /\ (forall x, In x KS_brvTO -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 751316
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 38%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G12 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI6 K4 K5 pvzI7 K7 K8 K9 K10 K11 K12 K13 pvzI8 K15 K16 K17 K18 K19 K20.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K6l; move K6l before pvzI7; pose proof (proj2 pvzI7) as K6r; move K6r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K14l; move K14l before pvzI8; pose proof (proj2 pvzI8) as K14r; move K14r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 48%nat. }
  assert (HR: regs_ok E PbrvTO.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbrvTO.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbrvTO.kn0).
  { unfold know_ok, PbrvTO.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbrvTO.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbrvTO.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbrvTO.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbrvTO.ps0) with 0xbb3f0 in Hms. change (SR.ps_regs PbrvTO.ps0) with (map (fun i => (i, nth i PbrvTO.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbrvTO.ps0) with PbrvTO.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbrvTO.regs0 PbrvTO.regs_out0 72 KS_brvTO KS_brvTO_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbrvTO.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbrvTO.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTO.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbrvTO.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTO.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbrvTO.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbrvTO.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbrvTO.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PbrvTS := BndP_Eb_045S9.LibSegEb_brvTS.
Definition KS_brvTS : list nat := Eval vm_compute in (BG.kept_list 72 PbrvTS.regs0 PbrvTS.regs_out0).
Lemma KS_brvTS_ok : BG.kept_ok 72 PbrvTS.regs0 PbrvTS.regs_out0 KS_brvTS = true. Proof. vm_compute. reflexivity. Qed.
Lemma brvTS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 12) = Z_to_bv 64 99 -> getr R (reg 18) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 47%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 (V 37%nat) -> getr R (reg 23) = Z_to_bv 64 83 -> getr R (reg 26) = Z_to_bv 64 (V 47%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6930432 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 128)) -> 6930432 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 128) + 128 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 128)) ->
  ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb754c M) (st fx' R' 0xba0f8 M')
        /\ (forall x, In x KS_brvTS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 751332
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 38%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G12 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI6 K4 K5 pvzI7 K7 K8 K9 K10 K11 K12 K13 pvzI8 K15 K16 K17 K18 K19 K20.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K6l; move K6l before pvzI7; pose proof (proj2 pvzI7) as K6r; move K6r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K14l; move K14l before pvzI8; pose proof (proj2 pvzI8) as K14r; move K14r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 48%nat. }
  assert (HR: regs_ok E PbrvTS.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbrvTS.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbrvTS.kn0).
  { unfold know_ok, PbrvTS.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbrvTS.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbrvTS.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbrvTS.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbrvTS.ps0) with 0xba0f8 in Hms. change (SR.ps_regs PbrvTS.ps0) with (map (fun i => (i, nth i PbrvTS.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbrvTS.ps0) with PbrvTS.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbrvTS.regs0 PbrvTS.regs_out0 72 KS_brvTS KS_brvTS_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbrvTS.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbrvTS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTS.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbrvTS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbrvTS.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbrvTS.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PbrvTH := BndP_Eb_045S9.LibSegEb_brvTH.
Definition KS_brvTH : list nat := Eval vm_compute in (BG.kept_list 72 PbrvTH.regs0 PbrvTH.regs_out0).
Lemma KS_brvTH_ok : BG.kept_ok 72 PbrvTH.regs0 PbrvTH.regs_out0 KS_brvTH = true. Proof. vm_compute. reflexivity. Qed.
Lemma brvTH_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 12) = Z_to_bv 64 99 -> getr R (reg 18) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 47%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 (V 37%nat) -> getr R (reg 23) = Z_to_bv 64 72 -> getr R (reg 26) = Z_to_bv 64 (V 47%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6930432 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 128)) -> 6930432 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 128) + 128 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 128)) ->
  ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb754c M) (st fx' R' 0xba0f8 M')
        /\ (forall x, In x KS_brvTH -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 751456
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 38%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G12 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI6 K4 K5 pvzI7 K7 K8 K9 K10 K11 K12 K13 pvzI8 K15 K16 K17 K18 K19 K20.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K6l; move K6l before pvzI7; pose proof (proj2 pvzI7) as K6r; move K6r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K14l; move K14l before pvzI8; pose proof (proj2 pvzI8) as K14r; move K14r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 48%nat. }
  assert (HR: regs_ok E PbrvTH.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbrvTH.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbrvTH.kn0).
  { unfold know_ok, PbrvTH.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbrvTH.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbrvTH.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbrvTH.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbrvTH.ps0) with 0xba0f8 in Hms. change (SR.ps_regs PbrvTH.ps0) with (map (fun i => (i, nth i PbrvTH.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbrvTH.ps0) with PbrvTH.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbrvTH.regs0 PbrvTH.regs_out0 72 KS_brvTH KS_brvTH_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbrvTH.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbrvTH.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTH.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbrvTH.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbrvTH.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbrvTH.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PbrvTC := BndP_Eb_044S9.LibSegEb_brvTC.
Definition KS_brvTC : list nat := Eval vm_compute in (BG.kept_list 72 PbrvTC.regs0 PbrvTC.regs_out0).
Lemma KS_brvTC_ok : BG.kept_ok 72 PbrvTC.regs0 PbrvTC.regs_out0 KS_brvTC = true. Proof. vm_compute. reflexivity. Qed.
Lemma brvTC_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 12) = Z_to_bv 64 99 -> getr R (reg 18) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 47%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 (V 37%nat) -> getr R (reg 23) = Z_to_bv 64 67 -> getr R (reg 26) = Z_to_bv 64 (V 47%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6930432 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 128)) -> 6930432 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 128) + 128 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 128)) ->
  ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) -> 6930432 <= (V 47%nat) <= 140737488354816 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 512 ->
  L5.writable RSEGS M (V 47%nat) 512 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 47%nat) + 504) (V 48%nat) ->
  4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 512 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) ->
  (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 512 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) -> ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 512 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) ->
  ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 64 <= (((V 36%nat) / 8) + 2147450880)) -> ((V 38%nat) + 16 <= (V 47%nat) \/ (V 47%nat) + 512 <= (V 38%nat)) -> ((V 38%nat) + 16 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 38%nat)) -> ((((V 38%nat) / 8) + 2147450880) + 2 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 64 <= (((V 38%nat) / 8) + 2147450880)) ->
  ((V 47%nat) + 512 <= 65536 \/ 65536 + 1241088 <= (V 47%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((((V 47%nat) / 8) + 2147450880) + 22) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 22) + 1) -> ~ (((V 47%nat) + 176) <= bv_unsigned a < ((V 47%nat) + 176) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((((V 47%nat) / 8) + 2147450880) + 22) <= i < ((((V 47%nat) / 8) + 2147450880) + 22) + 1) -> ~ (((V 47%nat) + 176) <= i < ((V 47%nat) + 176) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb754c M) (st fx' R' 0xb9148 M')
        /\ (forall x, In x KS_brvTC -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 751000
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 24)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 47%nat) + 176)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 47%nat) + 176)
        /\ getr R' (reg 24) = Z_to_bv 64 1
        /\ L5.u8_at RSEGS M' ((V 47%nat) + 176) 0
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450902) 1
        /\ L5.defined M' (V 47%nat) 176
        /\ L5.defined M' ((V 47%nat) + 177) 335).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G12 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 pvzI9 K15 K16 K17 K18 K19 K20 pvzI10 K22 K23 K24 K25 K26 K27 pvzI11 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K21l; move K21l before pvzI10; pose proof (proj2 pvzI10) as K21r; move K21r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K28l; move K28l before pvzI11; pose proof (proj2 pvzI11) as K28r; move K28r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PbrvTC.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbrvTC.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbrvTC.kn0).
  { unfold know_ok, PbrvTC.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | clear; lia | exact K22]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | exact (conj K28l K28r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K28l K28r; lia | clear - HV48l HV48r K28l K28r; lia | clear - HV48l HV48r K28l K28r; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbrvTC.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbrvTC.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((vz_47 / 8) + 2147450880) + 22) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 22) + 1) -> ~ ((vz_47 + 176) <= bv_unsigned a < (vz_47 + 176) + 1) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PbrvTC.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K21l K21r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K21l K21r Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbrvTC.ps0) with 0xb9148 in Hms. change (SR.ps_regs PbrvTC.ps0) with (map (fun i => (i, nth i PbrvTC.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbrvTC.ps0) with PbrvTC.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbrvTC.regs0 PbrvTC.regs_out0 72 KS_brvTC KS_brvTC_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbrvTC.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbrvTC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTC.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbrvTC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTC.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbrvTC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTC.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbrvTC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTC.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbrvTC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTC.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbrvTC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PbrvTi := BndP_Eb_045S9.LibSegEb_brvTi.
Definition KS_brvTi : list nat := Eval vm_compute in (BG.kept_list 72 PbrvTi.regs0 PbrvTi.regs_out0).
Lemma KS_brvTi_ok : BG.kept_ok 72 PbrvTi.regs0 PbrvTi.regs_out0 KS_brvTi = true. Proof. vm_compute. reflexivity. Qed.
Lemma brvTi_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 12) = Z_to_bv 64 99 -> getr R (reg 18) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 47%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 (V 37%nat) -> getr R (reg 23) = Z_to_bv 64 105 -> getr R (reg 26) = Z_to_bv 64 (V 47%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6930432 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 128)) -> 6930432 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 128) + 128 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 128)) ->
  ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) -> 6930432 <= (V 47%nat) <= 140737488354816 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 512 ->
  L5.writable RSEGS M (V 47%nat) 512 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 47%nat) + 504) (V 48%nat) ->
  4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 512 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) ->
  (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 512 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) -> ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 512 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) ->
  ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 64 <= (((V 36%nat) / 8) + 2147450880)) -> ((V 38%nat) + 16 <= (V 47%nat) \/ (V 47%nat) + 512 <= (V 38%nat)) -> ((V 38%nat) + 16 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 38%nat)) -> ((((V 38%nat) / 8) + 2147450880) + 2 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 64 <= (((V 38%nat) / 8) + 2147450880)) ->
  ((V 47%nat) + 512 <= 65536 \/ 65536 + 1241088 <= (V 47%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((((V 47%nat) / 8) + 2147450880) + 4) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 4) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((((V 47%nat) / 8) + 2147450880) + 4) <= i < ((((V 47%nat) / 8) + 2147450880) + 4) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb754c M) (st fx' R' 0xb9148 M')
        /\ (forall x, In x KS_brvTi -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 751128
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 24)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 47%nat) + 32)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 47%nat) + 32)
        /\ getr R' (reg 24) = Z_to_bv 64 1
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 1).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G12 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 pvzI9 K15 K16 K17 K18 K19 K20 pvzI10 K22 K23 K24 K25 K26 K27 pvzI11 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K21l; move K21l before pvzI10; pose proof (proj2 pvzI10) as K21r; move K21r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K28l; move K28l before pvzI11; pose proof (proj2 pvzI11) as K28r; move K28r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PbrvTi.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbrvTi.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbrvTi.kn0).
  { unfold know_ok, PbrvTi.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | clear; lia | exact K22]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | exact (conj K28l K28r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K28l K28r; lia | clear - HV48l HV48r K28l K28r; lia | clear - HV48l HV48r K28l K28r; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbrvTi.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbrvTi.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((vz_47 / 8) + 2147450880) + 4) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 4) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbrvTi.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K21l K21r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbrvTi.ps0) with 0xb9148 in Hms. change (SR.ps_regs PbrvTi.ps0) with (map (fun i => (i, nth i PbrvTi.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbrvTi.ps0) with PbrvTi.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbrvTi.regs0 PbrvTi.regs_out0 72 KS_brvTi KS_brvTi_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbrvTi.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbrvTi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTi.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbrvTi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTi.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbrvTi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTi.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbrvTi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTi.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbrvTi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTi.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbrvTi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.

Module PbrvTU := BndP_Eb_045S9.LibSegEb_brvTU.
Definition KS_brvTU : list nat := Eval vm_compute in (BG.kept_list 72 PbrvTU.regs0 PbrvTU.regs_out0).
Lemma KS_brvTU_ok : BG.kept_ok 72 PbrvTU.regs0 PbrvTU.regs_out0 KS_brvTU = true. Proof. vm_compute. reflexivity. Qed.
Lemma brvTU_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 12) = Z_to_bv 64 99 -> getr R (reg 18) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 47%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 (V 37%nat) -> getr R (reg 23) = Z_to_bv 64 85 -> getr R (reg 26) = Z_to_bv 64 (V 47%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6930432 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 128)) -> 6930432 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 128) + 128 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 128)) ->
  ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) -> 6930432 <= (V 47%nat) <= 140737488354816 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 512 ->
  L5.writable RSEGS M (V 47%nat) 512 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 47%nat) + 504) (V 48%nat) ->
  4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 512 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) ->
  (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 512 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) -> ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 512 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) ->
  ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 64 <= (((V 36%nat) / 8) + 2147450880)) -> ((V 38%nat) + 16 <= (V 47%nat) \/ (V 47%nat) + 512 <= (V 38%nat)) -> ((V 38%nat) + 16 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 38%nat)) -> ((((V 38%nat) / 8) + 2147450880) + 2 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 64 <= (((V 38%nat) / 8) + 2147450880)) ->
  ((V 47%nat) + 512 <= 65536 \/ 65536 + 1241088 <= (V 47%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((((V 47%nat) / 8) + 2147450880) + 6) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 6) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((((V 47%nat) / 8) + 2147450880) + 6) <= i < ((((V 47%nat) / 8) + 2147450880) + 6) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb754c M) (st fx' R' 0xb9148 M')
        /\ (forall x, In x KS_brvTU -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 752864
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 24)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 47%nat) + 48)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 47%nat) + 48)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 1).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G12 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 pvzI9 K15 K16 K17 K18 K19 K20 pvzI10 K22 K23 K24 K25 K26 K27 pvzI11 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K21l; move K21l before pvzI10; pose proof (proj2 pvzI10) as K21r; move K21r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K28l; move K28l before pvzI11; pose proof (proj2 pvzI11) as K28r; move K28r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PbrvTU.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbrvTU.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbrvTU.kn0).
  { unfold know_ok, PbrvTU.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | clear; lia | exact K22]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | exact (conj K28l K28r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K28l K28r; lia | clear - HV48l HV48r K28l K28r; lia | clear - HV48l HV48r K28l K28r; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbrvTU.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbrvTU.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((vz_47 / 8) + 2147450880) + 6) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 6) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbrvTU.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K21l K21r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbrvTU.ps0) with 0xb9148 in Hms. change (SR.ps_regs PbrvTU.ps0) with (map (fun i => (i, nth i PbrvTU.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbrvTU.ps0) with PbrvTU.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbrvTU.regs0 PbrvTU.regs_out0 72 KS_brvTU KS_brvTU_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbrvTU.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbrvTU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTU.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbrvTU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTU.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbrvTU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTU.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbrvTU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTU.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbrvTU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.

Module PbrvTI := BndP_Eb_045S9.LibSegEb_brvTI.
Definition KS_brvTI : list nat := Eval vm_compute in (BG.kept_list 72 PbrvTI.regs0 PbrvTI.regs_out0).
Lemma KS_brvTI_ok : BG.kept_ok 72 PbrvTI.regs0 PbrvTI.regs_out0 KS_brvTI = true. Proof. vm_compute. reflexivity. Qed.
Lemma brvTI_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 12) = Z_to_bv 64 99 -> getr R (reg 18) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 47%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 (V 37%nat) -> getr R (reg 23) = Z_to_bv 64 73 -> getr R (reg 26) = Z_to_bv 64 (V 47%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6930432 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 128)) -> 6930432 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 128) + 128 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 128)) ->
  ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) -> 6930432 <= (V 47%nat) <= 140737488354816 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 512 ->
  L5.writable RSEGS M (V 47%nat) 512 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 47%nat) + 504) (V 48%nat) ->
  4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 512 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) ->
  (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 512 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) -> ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 512 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) ->
  ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 64 <= (((V 36%nat) / 8) + 2147450880)) -> ((V 38%nat) + 16 <= (V 47%nat) \/ (V 47%nat) + 512 <= (V 38%nat)) -> ((V 38%nat) + 16 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 38%nat)) -> ((((V 38%nat) / 8) + 2147450880) + 2 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 64 <= (((V 38%nat) / 8) + 2147450880)) ->
  ((V 47%nat) + 512 <= 65536 \/ 65536 + 1241088 <= (V 47%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((((V 47%nat) / 8) + 2147450880) + 8) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 8) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((((V 47%nat) / 8) + 2147450880) + 8) <= i < ((((V 47%nat) / 8) + 2147450880) + 8) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb754c M) (st fx' R' 0xb9148 M')
        /\ (forall x, In x KS_brvTI -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 752096
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 24)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 47%nat) + 64)
        /\ getr R' (reg 12) = Z_to_bv 64 2
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 47%nat) + 64)
        /\ getr R' (reg 24) = Z_to_bv 64 2
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450888) 2).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G12 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 pvzI9 K15 K16 K17 K18 K19 K20 pvzI10 K22 K23 K24 K25 K26 K27 pvzI11 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K21l; move K21l before pvzI10; pose proof (proj2 pvzI10) as K21r; move K21r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K28l; move K28l before pvzI11; pose proof (proj2 pvzI11) as K28r; move K28r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PbrvTI.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbrvTI.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbrvTI.kn0).
  { unfold know_ok, PbrvTI.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | clear; lia | exact K22]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | exact (conj K28l K28r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K28l K28r; lia | clear - HV48l HV48r K28l K28r; lia | clear - HV48l HV48r K28l K28r; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbrvTI.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbrvTI.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((vz_47 / 8) + 2147450880) + 8) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 8) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbrvTI.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K21l K21r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbrvTI.ps0) with 0xb9148 in Hms. change (SR.ps_regs PbrvTI.ps0) with (map (fun i => (i, nth i PbrvTI.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbrvTI.ps0) with PbrvTI.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbrvTI.regs0 PbrvTI.regs_out0 72 KS_brvTI KS_brvTI_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbrvTI.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbrvTI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTI.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbrvTI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTI.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbrvTI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTI.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbrvTI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTI.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbrvTI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTI.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbrvTI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.

Module PbrvTl := BndP_Eb_045S9.LibSegEb_brvTl.
Definition KS_brvTl : list nat := Eval vm_compute in (BG.kept_list 72 PbrvTl.regs0 PbrvTl.regs_out0).
Lemma KS_brvTl_ok : BG.kept_ok 72 PbrvTl.regs0 PbrvTl.regs_out0 KS_brvTl = true. Proof. vm_compute. reflexivity. Qed.
Lemma brvTl_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 12) = Z_to_bv 64 99 -> getr R (reg 18) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 47%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 (V 37%nat) -> getr R (reg 23) = Z_to_bv 64 108 -> getr R (reg 26) = Z_to_bv 64 (V 47%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6930432 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 128)) -> 6930432 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 128) + 128 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 128)) ->
  ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) -> 6930432 <= (V 47%nat) <= 140737488354816 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 512 ->
  L5.writable RSEGS M (V 47%nat) 512 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 47%nat) + 504) (V 48%nat) ->
  4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 512 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) ->
  (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 512 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) -> ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 512 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) ->
  ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 64 <= (((V 36%nat) / 8) + 2147450880)) -> ((V 38%nat) + 16 <= (V 47%nat) \/ (V 47%nat) + 512 <= (V 38%nat)) -> ((V 38%nat) + 16 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 38%nat)) -> ((((V 38%nat) / 8) + 2147450880) + 2 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 64 <= (((V 38%nat) / 8) + 2147450880)) ->
  ((V 47%nat) + 512 <= 65536 \/ 65536 + 1241088 <= (V 47%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((((V 47%nat) / 8) + 2147450880) + 10) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 10) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((((V 47%nat) / 8) + 2147450880) + 10) <= i < ((((V 47%nat) / 8) + 2147450880) + 10) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb754c M) (st fx' R' 0xb9148 M')
        /\ (forall x, In x KS_brvTl -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 753268
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 24)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 47%nat) + 80)
        /\ getr R' (reg 12) = Z_to_bv 64 4
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 47%nat) + 80)
        /\ getr R' (reg 24) = Z_to_bv 64 4
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450890) 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G12 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 pvzI9 K15 K16 K17 K18 K19 K20 pvzI10 K22 K23 K24 K25 K26 K27 pvzI11 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K21l; move K21l before pvzI10; pose proof (proj2 pvzI10) as K21r; move K21r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K28l; move K28l before pvzI11; pose proof (proj2 pvzI11) as K28r; move K28r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PbrvTl.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbrvTl.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbrvTl.kn0).
  { unfold know_ok, PbrvTl.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | clear; lia | exact K22]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | exact (conj K28l K28r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K28l K28r; lia | clear - HV48l HV48r K28l K28r; lia | clear - HV48l HV48r K28l K28r; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbrvTl.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbrvTl.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((vz_47 / 8) + 2147450880) + 10) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 10) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbrvTl.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K21l K21r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbrvTl.ps0) with 0xb9148 in Hms. change (SR.ps_regs PbrvTl.ps0) with (map (fun i => (i, nth i PbrvTl.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbrvTl.ps0) with PbrvTl.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbrvTl.regs0 PbrvTl.regs_out0 72 KS_brvTl KS_brvTl_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbrvTl.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbrvTl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTl.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbrvTl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTl.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbrvTl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTl.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbrvTl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTl.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbrvTl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTl.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbrvTl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.

Module PbrvTL := BndP_Eb_045S9.LibSegEb_brvTL.
Definition KS_brvTL : list nat := Eval vm_compute in (BG.kept_list 72 PbrvTL.regs0 PbrvTL.regs_out0).
Lemma KS_brvTL_ok : BG.kept_ok 72 PbrvTL.regs0 PbrvTL.regs_out0 KS_brvTL = true. Proof. vm_compute. reflexivity. Qed.
Lemma brvTL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 12) = Z_to_bv 64 99 -> getr R (reg 18) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 47%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 (V 37%nat) -> getr R (reg 23) = Z_to_bv 64 76 -> getr R (reg 26) = Z_to_bv 64 (V 47%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6930432 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 128)) -> 6930432 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 128) + 128 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 128)) ->
  ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) -> 6930432 <= (V 47%nat) <= 140737488354816 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 512 ->
  L5.writable RSEGS M (V 47%nat) 512 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 47%nat) + 504) (V 48%nat) ->
  4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 512 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) ->
  (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 512 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) -> ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 512 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) ->
  ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 64 <= (((V 36%nat) / 8) + 2147450880)) -> ((V 38%nat) + 16 <= (V 47%nat) \/ (V 47%nat) + 512 <= (V 38%nat)) -> ((V 38%nat) + 16 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 38%nat)) -> ((((V 38%nat) / 8) + 2147450880) + 2 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 64 <= (((V 38%nat) / 8) + 2147450880)) ->
  ((V 47%nat) + 512 <= 65536 \/ 65536 + 1241088 <= (V 47%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((((V 47%nat) / 8) + 2147450880) + 12) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 12) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((((V 47%nat) / 8) + 2147450880) + 12) <= i < ((((V 47%nat) / 8) + 2147450880) + 12) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb754c M) (st fx' R' 0xb9148 M')
        /\ (forall x, In x KS_brvTL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 752288
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 24)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 47%nat) + 96)
        /\ getr R' (reg 12) = Z_to_bv 64 8
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 47%nat) + 96)
        /\ getr R' (reg 24) = Z_to_bv 64 8
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450892) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G12 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 pvzI9 K15 K16 K17 K18 K19 K20 pvzI10 K22 K23 K24 K25 K26 K27 pvzI11 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K21l; move K21l before pvzI10; pose proof (proj2 pvzI10) as K21r; move K21r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K28l; move K28l before pvzI11; pose proof (proj2 pvzI11) as K28r; move K28r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PbrvTL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbrvTL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbrvTL.kn0).
  { unfold know_ok, PbrvTL.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | clear; lia | exact K22]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | exact (conj K28l K28r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K28l K28r; lia | clear - HV48l HV48r K28l K28r; lia | clear - HV48l HV48r K28l K28r; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbrvTL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbrvTL.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((vz_47 / 8) + 2147450880) + 12) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 12) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbrvTL.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K21l K21r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbrvTL.ps0) with 0xb9148 in Hms. change (SR.ps_regs PbrvTL.ps0) with (map (fun i => (i, nth i PbrvTL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbrvTL.ps0) with PbrvTL.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbrvTL.regs0 PbrvTL.regs_out0 72 KS_brvTL KS_brvTL_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbrvTL.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbrvTL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTL.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbrvTL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTL.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbrvTL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTL.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbrvTL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTL.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbrvTL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTL.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbrvTL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.

Module PbrvTd := BndP_Eb_045S9.LibSegEb_brvTd.
Definition KS_brvTd : list nat := Eval vm_compute in (BG.kept_list 72 PbrvTd.regs0 PbrvTd.regs_out0).
Lemma KS_brvTd_ok : BG.kept_ok 72 PbrvTd.regs0 PbrvTd.regs_out0 KS_brvTd = true. Proof. vm_compute. reflexivity. Qed.
Lemma brvTd_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 12) = Z_to_bv 64 99 -> getr R (reg 18) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 47%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 (V 37%nat) -> getr R (reg 23) = Z_to_bv 64 100 -> getr R (reg 26) = Z_to_bv 64 (V 47%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6930432 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 128)) -> 6930432 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 128) + 128 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 128)) ->
  ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) -> 6930432 <= (V 47%nat) <= 140737488354816 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 512 ->
  L5.writable RSEGS M (V 47%nat) 512 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 47%nat) + 504) (V 48%nat) ->
  4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 512 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) ->
  (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 512 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) -> ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 512 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) ->
  ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 64 <= (((V 36%nat) / 8) + 2147450880)) -> ((V 38%nat) + 16 <= (V 47%nat) \/ (V 47%nat) + 512 <= (V 38%nat)) -> ((V 38%nat) + 16 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 38%nat)) -> ((((V 38%nat) / 8) + 2147450880) + 2 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 64 <= (((V 38%nat) / 8) + 2147450880)) ->
  ((V 47%nat) + 512 <= 65536 \/ 65536 + 1241088 <= (V 47%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((((V 47%nat) / 8) + 2147450880) + 16) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 16) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((((V 47%nat) / 8) + 2147450880) + 16) <= i < ((((V 47%nat) / 8) + 2147450880) + 16) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb754c M) (st fx' R' 0xb9148 M')
        /\ (forall x, In x KS_brvTd -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 753040
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 24)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 47%nat) + 128)
        /\ getr R' (reg 12) = Z_to_bv 64 4
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 47%nat) + 128)
        /\ getr R' (reg 24) = Z_to_bv 64 4
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450896) 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G12 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 pvzI9 K15 K16 K17 K18 K19 K20 pvzI10 K22 K23 K24 K25 K26 K27 pvzI11 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K21l; move K21l before pvzI10; pose proof (proj2 pvzI10) as K21r; move K21r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K28l; move K28l before pvzI11; pose proof (proj2 pvzI11) as K28r; move K28r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PbrvTd.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbrvTd.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbrvTd.kn0).
  { unfold know_ok, PbrvTd.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | clear; lia | exact K22]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | exact (conj K28l K28r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K28l K28r; lia | clear - HV48l HV48r K28l K28r; lia | clear - HV48l HV48r K28l K28r; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbrvTd.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbrvTd.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((vz_47 / 8) + 2147450880) + 16) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 16) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbrvTd.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K21l K21r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbrvTd.ps0) with 0xb9148 in Hms. change (SR.ps_regs PbrvTd.ps0) with (map (fun i => (i, nth i PbrvTd.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbrvTd.ps0) with PbrvTd.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbrvTd.regs0 PbrvTd.regs_out0 72 KS_brvTd KS_brvTd_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbrvTd.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbrvTd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTd.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbrvTd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTd.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbrvTd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTd.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbrvTd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTd.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbrvTd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTd.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbrvTd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.

Module PbrvTD := BndP_Eb_044S9.LibSegEb_brvTD.
Definition KS_brvTD : list nat := Eval vm_compute in (BG.kept_list 72 PbrvTD.regs0 PbrvTD.regs_out0).
Lemma KS_brvTD_ok : BG.kept_ok 72 PbrvTD.regs0 PbrvTD.regs_out0 KS_brvTD = true. Proof. vm_compute. reflexivity. Qed.
Lemma brvTD_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 12) = Z_to_bv 64 99 -> getr R (reg 18) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 47%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 (V 37%nat) -> getr R (reg 23) = Z_to_bv 64 68 -> getr R (reg 26) = Z_to_bv 64 (V 47%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6930432 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 128)) -> 6930432 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 128) + 128 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 128)) ->
  ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) -> 6930432 <= (V 47%nat) <= 140737488354816 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 512 ->
  L5.writable RSEGS M (V 47%nat) 512 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 47%nat) + 504) (V 48%nat) ->
  4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 512 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) ->
  (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 512 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) -> ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 512 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) ->
  ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 64 <= (((V 36%nat) / 8) + 2147450880)) -> ((V 38%nat) + 16 <= (V 47%nat) \/ (V 47%nat) + 512 <= (V 38%nat)) -> ((V 38%nat) + 16 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 38%nat)) -> ((((V 38%nat) / 8) + 2147450880) + 2 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 64 <= (((V 38%nat) / 8) + 2147450880)) ->
  ((V 47%nat) + 512 <= 65536 \/ 65536 + 1241088 <= (V 47%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((((V 47%nat) / 8) + 2147450880) + 18) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 18) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((((V 47%nat) / 8) + 2147450880) + 18) <= i < ((((V 47%nat) / 8) + 2147450880) + 18) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb754c M) (st fx' R' 0xb9148 M')
        /\ (forall x, In x KS_brvTD -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 752584
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 24)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 47%nat) + 144)
        /\ getr R' (reg 12) = Z_to_bv 64 8
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 47%nat) + 144)
        /\ getr R' (reg 24) = Z_to_bv 64 8
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450898) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G12 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 pvzI9 K15 K16 K17 K18 K19 K20 pvzI10 K22 K23 K24 K25 K26 K27 pvzI11 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K21l; move K21l before pvzI10; pose proof (proj2 pvzI10) as K21r; move K21r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K28l; move K28l before pvzI11; pose proof (proj2 pvzI11) as K28r; move K28r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PbrvTD.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbrvTD.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbrvTD.kn0).
  { unfold know_ok, PbrvTD.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | clear; lia | exact K22]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | clear - HV47l HV47r K21l K21r; lia | clear - HV47l HV47r K21l K21r; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | exact (conj K28l K28r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K28l K28r; lia | clear - HV48l HV48r K28l K28r; lia | clear - HV48l HV48r K28l K28r; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K28l K28r) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K21l K21r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbrvTD.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbrvTD.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((vz_47 / 8) + 2147450880) + 18) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 18) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbrvTD.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K21l K21r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbrvTD.ps0) with 0xb9148 in Hms. change (SR.ps_regs PbrvTD.ps0) with (map (fun i => (i, nth i PbrvTD.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbrvTD.ps0) with PbrvTD.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbrvTD.regs0 PbrvTD.regs_out0 72 KS_brvTD KS_brvTD_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbrvTD.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbrvTD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTD.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbrvTD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTD.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbrvTD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTD.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbrvTD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTD.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbrvTD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrvTD.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbrvTD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K21l K21r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.

End PEBRVP1.
