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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.seg Require BndP_Ea_048S8 BndP_Ea_049S8 BndP_Ea_050S8.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEASKPP.
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

Module PaskA := BndP_Ea_048S8.LibSegEa_askA.
Definition KS_askA : list nat := Eval vm_compute in (BG.kept_list 60 PaskA.regs0 PaskA.regs_out0).
Lemma KS_askA_ok : BG.kept_ok 60 PaskA.regs0 PaskA.regs_out0 KS_askA = true. Proof. vm_compute. reflexivity. Qed.
Lemma askA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  L5.img_clear M 1253376 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487216 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 6914048 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 -> aligned (bv_unsigned (getr R (reg 10))) 8 ->
  (2147446784 + 17592186048512 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= 2147446784) -> L5KA.zeros_at M (((bv_unsigned (getr R (reg 10))) / 8) + 2147450880) 3 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 -> (((V 2%nat) - 256) + 256 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= ((V 2%nat) - 256)) ->
  4096 <= (bv_unsigned (getr R (reg 11))) <= 140737488355327 -> (2147446784 + 17592186048512 <= (bv_unsigned (getr R (reg 11))) \/ (bv_unsigned (getr R (reg 11))) + 1 <= 2147446784) -> L5KA.zeros_at M (((bv_unsigned (getr R (reg 11))) / 8) + 2147450880) 1 -> L5.u8_at RSEGS M (bv_unsigned (getr R (reg 11))) (V 40%nat) ->
  0 <= (V 40%nat) <= 255 -> ((bv_unsigned (getr R (reg 11))) + 1 <= ((V 2%nat) - 256) \/ ((V 2%nat) - 256) + 256 <= (bv_unsigned (getr R (reg 11)))) -> ((bv_unsigned (getr R (reg 11))) + 1 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= (bv_unsigned (getr R (reg 11)))) -> L5.u64_at RSEGS M (bv_unsigned (getr R (reg 10))) (V 33%nat) ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) ((V 33%nat) + (V 34%nat)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 16) ((V 33%nat) + (V 35%nat)) -> 4096 <= (V 33%nat) <= 140737488355328 -> aligned (V 33%nat) 16 ->
  0 <= (V 34%nat) <= 17179869184 -> 0 <= (V 35%nat) <= 17179869184 -> 4096 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + (V 35%nat) <= 2147446784) ->
  (65536 + 6848512 <= (V 33%nat) \/ (V 33%nat) + (V 35%nat) <= 65536) -> 1 <= ((V 35%nat) - (V 34%nat)) <= 17179869184 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xaf02c M) (st fx' R' 0xaf310 M')
        /\ (forall x, In x KS_askA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 716948
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 8) = Z_to_bv 64 ((bv_unsigned (getr R (reg 10))) + 8)
        /\ getr R' (reg 9) = getr R (reg 11)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 33%nat) + (V 34%nat))
        /\ getr R' (reg 19) = Z_to_bv 64 ((((bv_unsigned (getr R (reg 10))) + 8) / 8) + 2147450880)
        /\ getr R' (reg 20) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 K0 K1 K2 pvzI6 K4 K5 pvzI7 K7 K8 K9 K10 K11 pvzI8 K13 K14 K15 pvzI9 K17 K18 K19 K20 K21 pvzI10 K23 pvzI11 pvzI12 pvzI13 K27 K28 pvzI14.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV40l; move HV40l before pvzI5; pose proof (proj2 pvzI5) as HV40r; move HV40r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K6l; move K6l before pvzI7; pose proof (proj2 pvzI7) as K6r; move K6r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K12l; move K12l before pvzI8; pose proof (proj2 pvzI8) as K12r; move K12r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K16l; move K16l before pvzI9; pose proof (proj2 pvzI9) as K16r; move K16r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K22l; move K22l before pvzI10; pose proof (proj2 pvzI10) as K22r; move K22r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K24l; move K24l before pvzI11; pose proof (proj2 pvzI11) as K24r; move K24r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K25l; move K25l before pvzI12; pose proof (proj2 pvzI12) as K25r; move K25r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K26l; move K26l before pvzI13; pose proof (proj2 pvzI13) as K26r; move K26r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K29l; move K29l before pvzI14; pose proof (proj2 pvzI14) as K29r; move K29r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_40 := V 40%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 40%nat => Z_to_bv 64 vz_40 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 40%nat => vz_40 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 41%nat. }
  assert (HR: regs_ok E PaskA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaskA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaskA.kn0).
  { unfold know_ok, PaskA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K17; lia | clear - HV2l HV2r K3l K3r K11 K17; lia | clear - HV2l HV2r K3l K3r K11 K17; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K6l K6r K8 K11 K18) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K6l K6r K8 K11 K18) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | clear - K6l K6r K8 K11 K18; lia | clear - K6l K6r K8 K11 K18; lia | clear - K6l K6r K8 K11 K18; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | clear - K6l K6r K8 K11 K18; lia | clear - K6l K6r K8 K11 K18; lia | clear - K6l K6r K8 K11 K18; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K12l K12r K13 K17 K18) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K12l K12r K13 K17 K18) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - K12l K12r K13 K17 K18) | evalEk ZA ltac:(clear) | clear - K12l K12r K13 K17 K18; lia | clear - K12l K12r K13 K17 K18; lia | clear - K12l K12r K13 K17 K18; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - K12l K12r K13 K17 K18) | evalEk ZA ltac:(clear - HV40l HV40r K16l K16r) | clear - K12l K12r K13 K17 K18; lia | clear - K12l K12r K13 K17 K18; lia | byte_tac ltac:(clear - HV40l HV40r K16l K16r) | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - K12l K12r K13 K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - K12l K12r K13 K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear - HV33l HV33r K22l K22r K26l K26r K27 K28) | clear - K6l K6r K8 K11 K18; lia | clear - K6l K6r K8 K11 K18; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear - HV33l HV33r K22l K22r K26l K26r K27 K28 HV34l HV34r K24l K24r K29l K29r) | clear - K6l K6r K8 K11 K18; lia | clear - K6l K6r K8 K11 K18; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear - HV33l HV33r K22l K22r K26l K26r K27 K28 HV35l HV35r K25l K25r K29l K29r) | clear - K6l K6r K8 K11 K18; lia | clear - K6l K6r K8 K11 K18; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K22l K22r K26l K26r K27 K28) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K22l K22r K26l K26r K27 K28) | clear; lia | exact K23]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K24l K24r K29l K29r) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K25l K25r K26l K26r K27 K28 K29l K29r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K22l K22r K26l K26r K27 K28 HV35l HV35r K25l K25r K29l K29r) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K22l K22r K26l K26r K27 K28) | evalEk ZA ltac:(clear - HV35l HV35r K25l K25r K26l K26r K27 K28 K29l K29r) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K22l K22r K26l K26r K27 K28) | evalEk ZA ltac:(clear - HV35l HV35r K25l K25r K26l K26r K27 K28 K29l K29r) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K24l K24r K29l K29r HV35l HV35r K25l K25r K26l K26r K27 K28) | exact (conj K29l K29r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaskA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaskA.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PaskA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K17 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaskA.ps0) with 0xaf310 in Hms. change (SR.ps_regs PaskA.ps0) with (map (fun i => (i, nth i PaskA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaskA.ps0) with PaskA.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaskA.regs0 PaskA.regs_out0 60 KS_askA KS_askA_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaskA.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaskA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskA.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaskA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskA.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaskA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskA.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PaskA.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PaskA.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaskA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskA.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PaskA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskA.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaskA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskA.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaskA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskA.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PaskA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PaskAS := BndP_Ea_049S8.LibSegEa_askAS.
Definition KS_askAS : list nat := Eval vm_compute in (BG.kept_list 60 PaskAS.regs0 PaskAS.regs_out0).
Lemma KS_askAS_ok : BG.kept_ok 60 PaskAS.regs0 PaskAS.regs_out0 KS_askAS = true. Proof. vm_compute. reflexivity. Qed.
Lemma askAS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  L5.img_clear M 1253376 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487216 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 6914048 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 -> aligned (bv_unsigned (getr R (reg 10))) 8 ->
  (2147446784 + 17592186048512 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= 2147446784) -> L5KA.zeros_at M (((bv_unsigned (getr R (reg 10))) / 8) + 2147450880) 3 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 -> (((V 2%nat) - 256) + 256 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= ((V 2%nat) - 256)) ->
  4096 <= (bv_unsigned (getr R (reg 11))) <= 140737488355327 -> (2147446784 + 17592186048512 <= (bv_unsigned (getr R (reg 11))) \/ (bv_unsigned (getr R (reg 11))) + 1 <= 2147446784) -> L5KA.zeros_at M (((bv_unsigned (getr R (reg 11))) / 8) + 2147450880) 1 -> L5.u8_at RSEGS M (bv_unsigned (getr R (reg 11))) (V 40%nat) ->
  0 <= (V 40%nat) <= 255 -> ((bv_unsigned (getr R (reg 11))) + 1 <= ((V 2%nat) - 256) \/ ((V 2%nat) - 256) + 256 <= (bv_unsigned (getr R (reg 11)))) -> ((bv_unsigned (getr R (reg 11))) + 1 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= (bv_unsigned (getr R (reg 11)))) -> L5.u64_at RSEGS M (bv_unsigned (getr R (reg 10))) (V 33%nat) ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) ((V 33%nat) + (V 34%nat)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 16) ((V 33%nat) + (V 34%nat)) -> 0 <= (V 33%nat) <= 140737488355328 -> 0 <= (V 34%nat) <= 17179869184 ->
  0 <= (V 35%nat) <= 17179869184 -> 0 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xaf02c M) (st fx' R' 0xaf130 M')
        /\ (forall x, In x KS_askAS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 717004
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 8) = Z_to_bv 64 ((bv_unsigned (getr R (reg 10))) + 8)
        /\ getr R' (reg 9) = getr R (reg 11)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 33%nat) + (V 34%nat))
        /\ getr R' (reg 19) = Z_to_bv 64 ((((bv_unsigned (getr R (reg 10))) + 8) / 8) + 2147450880)
        /\ getr R' (reg 20) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 K0 K1 K2 pvzI6 K4 K5 pvzI7 K7 K8 K9 K10 K11 pvzI8 K13 K14 K15 pvzI9 K17 K18 K19 K20 K21 pvzI10 pvzI11 pvzI12 pvzI13.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV40l; move HV40l before pvzI5; pose proof (proj2 pvzI5) as HV40r; move HV40r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K6l; move K6l before pvzI7; pose proof (proj2 pvzI7) as K6r; move K6r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K12l; move K12l before pvzI8; pose proof (proj2 pvzI8) as K12r; move K12r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K16l; move K16l before pvzI9; pose proof (proj2 pvzI9) as K16r; move K16r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K22l; move K22l before pvzI10; pose proof (proj2 pvzI10) as K22r; move K22r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K23l; move K23l before pvzI11; pose proof (proj2 pvzI11) as K23r; move K23r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K24l; move K24l before pvzI12; pose proof (proj2 pvzI12) as K24r; move K24r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K25l; move K25l before pvzI13; pose proof (proj2 pvzI13) as K25r; move K25r before pvzI13; clear pvzI13.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_40 := V 40%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 40%nat => Z_to_bv 64 vz_40 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 40%nat => vz_40 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 41%nat. }
  assert (HR: regs_ok E PaskAS.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaskAS.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaskAS.kn0).
  { unfold know_ok, PaskAS.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K17; lia | clear - HV2l HV2r K3l K3r K11 K17; lia | clear - HV2l HV2r K3l K3r K11 K17; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K6l K6r K8 K11 K18) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K6l K6r K8 K11 K18) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | clear - K6l K6r K8 K11 K18; lia | clear - K6l K6r K8 K11 K18; lia | clear - K6l K6r K8 K11 K18; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | clear - K6l K6r K8 K11 K18; lia | clear - K6l K6r K8 K11 K18; lia | clear - K6l K6r K8 K11 K18; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K12l K12r K13 K17 K18) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K12l K12r K13 K17 K18) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - K12l K12r K13 K17 K18) | evalEk ZA ltac:(clear) | clear - K12l K12r K13 K17 K18; lia | clear - K12l K12r K13 K17 K18; lia | clear - K12l K12r K13 K17 K18; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - K12l K12r K13 K17 K18) | evalEk ZA ltac:(clear - HV40l HV40r K16l K16r) | clear - K12l K12r K13 K17 K18; lia | clear - K12l K12r K13 K17 K18; lia | byte_tac ltac:(clear - HV40l HV40r K16l K16r) | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - K12l K12r K13 K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - K12l K12r K13 K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear - HV33l HV33r K22l K22r K25l K25r) | clear - K6l K6r K8 K11 K18; lia | clear - K6l K6r K8 K11 K18; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear - HV33l HV33r K22l K22r K25l K25r HV34l HV34r K23l K23r) | clear - K6l K6r K8 K11 K18; lia | clear - K6l K6r K8 K11 K18; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear - HV33l HV33r K22l K22r K25l K25r HV34l HV34r K23l K23r) | clear - K6l K6r K8 K11 K18; lia | clear - K6l K6r K8 K11 K18; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K22l K22r K25l K25r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K25l K25r) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K22l K22r K25l K25r HV35l HV35r K24l K24r) | exact (conj K25l K25r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaskAS.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaskAS.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PaskAS.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K17 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaskAS.ps0) with 0xaf130 in Hms. change (SR.ps_regs PaskAS.ps0) with (map (fun i => (i, nth i PaskAS.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaskAS.ps0) with PaskAS.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaskAS.regs0 PaskAS.regs_out0 60 KS_askAS KS_askAS_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaskAS.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaskAS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskAS.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaskAS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskAS.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaskAS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskAS.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PaskAS.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PaskAS.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PaskAS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskAS.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaskAS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskAS.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaskAS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskAS.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PaskAS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PaskB7 := BndP_Ea_049S8.LibSegEa_askB7.
Definition KS_askB7 : list nat := Eval vm_compute in (BG.kept_list 60 PaskB7.regs0 PaskB7.regs_out0).
Lemma KS_askB7_ok : BG.kept_ok 60 PaskB7.regs0 PaskB7.regs_out0 KS_askB7 = true. Proof. vm_compute. reflexivity. Qed.
Lemma askB7_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + (V 34%nat)) -> getr R (reg 19) = Z_to_bv 64 ((((V 10%nat) + 8) / 8) + 2147450880) -> getr R (reg 20) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1253376 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487216 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 6914048 <= (V 10%nat) <= 140737488355304 -> aligned (V 10%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 10%nat) 24 -> (((V 2%nat) - 256) + 256 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 256)) ->
  4096 <= (V 36%nat) <= 140737488355327 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 1 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 1 -> L5.u8_at RSEGS M (V 36%nat) (V 40%nat) ->
  0 <= (V 40%nat) <= 255 -> ((V 36%nat) + 1 <= ((V 2%nat) - 256) \/ ((V 2%nat) - 256) + 256 <= (V 36%nat)) -> ((V 36%nat) + 1 <= (V 10%nat) \/ (V 10%nat) + 24 <= (V 36%nat)) -> 4096 <= (V 33%nat) <= 140737488355328 ->
  aligned (V 33%nat) 16 -> 0 <= (V 34%nat) <= 17179869184 -> 0 <= (V 35%nat) <= 17179869184 -> 4096 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + (V 35%nat) <= 2147446784) -> (65536 + 6848512 <= (V 33%nat) \/ (V 33%nat) + (V 35%nat) <= 65536) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) ->
  L5.writable RSEGS M ((V 33%nat) + (V 34%nat)) 1 -> (2147446784 + 17592186048512 <= ((V 33%nat) + (V 34%nat)) \/ ((V 33%nat) + (V 34%nat)) + 1 <= 2147446784) -> (((V 33%nat) + (V 34%nat)) + 1 <= ((V 2%nat) - 256) \/ ((V 2%nat) - 256) + 256 <= ((V 33%nat) + (V 34%nat))) -> (((V 33%nat) + (V 34%nat)) + 1 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 33%nat) + (V 34%nat))) ->
  (((V 33%nat) + (V 34%nat)) + 1 <= (V 36%nat) \/ (V 36%nat) + 1 <= ((V 33%nat) + (V 34%nat))) -> L5KA.zeros_at M ((((V 33%nat) + (V 34%nat)) / 8) + 2147450880) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((((V 33%nat) + (V 34%nat)) + 0) <= bv_unsigned a < (((V 33%nat) + (V 34%nat)) + 0) + 1) -> ~ (((V 10%nat) + 8) <= bv_unsigned a < ((V 10%nat) + 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((((V 33%nat) + (V 34%nat)) + 0) <= i < (((V 33%nat) + (V 34%nat)) + 0) + 1) -> ~ (((V 10%nat) + 8) <= i < ((V 10%nat) + 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xaf094 M) (st fx' R' 0xaf0f4 M')
        /\ (forall x, In x KS_askB7 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 33%nat) + (V 34%nat)) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 10%nat) + 8) (((V 33%nat) + (V 34%nat)) + 1)
        /\ L5.u8_at RSEGS M' ((V 33%nat) + (V 34%nat)) (V 40%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 G2 G8 G9 G10 G11 G12 G18 G19 G20 K0 K1 K2 pvzI17 K4 K5 pvzI18 K7 K8 K9 K10 K11 pvzI19 K13 K14 K15 pvzI20 K17 K18 pvzI21 K20 pvzI22 pvzI23 pvzI24 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV35l; move HV35l before pvzI5; pose proof (proj2 pvzI5) as HV35r; move HV35r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV36l; move HV36l before pvzI6; pose proof (proj2 pvzI6) as HV36r; move HV36r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV40l; move HV40l before pvzI7; pose proof (proj2 pvzI7) as HV40r; move HV40r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV44l; move HV44l before pvzI8; pose proof (proj2 pvzI8) as HV44r; move HV44r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV45l; move HV45l before pvzI9; pose proof (proj2 pvzI9) as HV45r; move HV45r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV46l; move HV46l before pvzI10; pose proof (proj2 pvzI10) as HV46r; move HV46r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV47l; move HV47l before pvzI11; pose proof (proj2 pvzI11) as HV47r; move HV47r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV48l; move HV48l before pvzI12; pose proof (proj2 pvzI12) as HV48r; move HV48r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV49l; move HV49l before pvzI13; pose proof (proj2 pvzI13) as HV49r; move HV49r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV55l; move HV55l before pvzI14; pose proof (proj2 pvzI14) as HV55r; move HV55r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV56l; move HV56l before pvzI15; pose proof (proj2 pvzI15) as HV56r; move HV56r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV57l; move HV57l before pvzI16; pose proof (proj2 pvzI16) as HV57r; move HV57r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K3l; move K3l before pvzI17; pose proof (proj2 pvzI17) as K3r; move K3r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K6l; move K6l before pvzI18; pose proof (proj2 pvzI18) as K6r; move K6r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K12l; move K12l before pvzI19; pose proof (proj2 pvzI19) as K12r; move K12r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K16l; move K16l before pvzI20; pose proof (proj2 pvzI20) as K16r; move K16r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K19l; move K19l before pvzI21; pose proof (proj2 pvzI21) as K19r; move K19r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K21l; move K21l before pvzI22; pose proof (proj2 pvzI22) as K21r; move K21r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K22l; move K22l before pvzI23; pose proof (proj2 pvzI23) as K22r; move K22r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K23l; move K23l before pvzI24; pose proof (proj2 pvzI24) as K23r; move K23r before pvzI24; clear pvzI24.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 40%nat => Z_to_bv 64 vz_40 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 40%nat => vz_40 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PaskB7.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaskB7.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaskB7.kn0).
  { unfold know_ok, PaskB7.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17 K34) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17 K34) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17 K34) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K17 K34; lia | clear - HV2l HV2r K3l K3r K11 K17 K34; lia | clear - HV2l HV2r K3l K3r K11 K17 K34; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11 K18 K35) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11 K18 K35) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11 K18 K35) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11 K18 K35) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K6l K6r K8 K11 K18 K35; lia | clear - HV10l HV10r K6l K6r K8 K11 K18 K35; lia | clear - HV10l HV10r K6l K6r K8 K11 K18 K35; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11 K18 K35) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K6l K6r K8 K11 K18 K35; lia | clear - HV10l HV10r K6l K6r K8 K11 K18 K35; lia | clear - HV10l HV10r K6l K6r K8 K11 K18 K35; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11 K18 K35) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K13 K17 K18 K36) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K13 K17 K18 K36) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K13 K17 K18 K36) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K12l K12r K13 K17 K18 K36; lia | clear - HV36l HV36r K12l K12r K13 K17 K18 K36; lia | clear - HV36l HV36r K12l K12r K13 K17 K18 K36; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K13 K17 K18 K36) | evalEk ZA ltac:(clear - HV40l HV40r K16l K16r) | clear - HV36l HV36r K12l K12r K13 K17 K18 K36; lia | clear - HV36l HV36r K12l K12r K13 K17 K18 K36; lia | byte_tac ltac:(clear - HV40l HV40r K16l K16r) | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K13 K17 K18 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17 K34) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K13 K17 K18 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11 K18 K35) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K23l K23r K24 K25 K33 K34 K35 K36) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K23l K23r K24 K25 K33 K34 K35 K36) | clear; lia | exact K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K21l K21r K33 K34 K35 K36) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K22l K22r K23l K23r K24 K25) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K23l K23r K24 K25 K33 K34 K35 K36 HV35l HV35r K22l K22r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K23l K23r K24 K25 K33 K34 K35 K36) | evalEk ZA ltac:(clear - HV35l HV35r K22l K22r K23l K23r K24 K25) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K23l K23r K24 K25 K33 K34 K35 K36) | evalEk ZA ltac:(clear - HV35l HV35r K22l K22r K23l K23r K24 K25) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17 K34) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K3l K3r K11 K17 K34; lia | clear - HV2l HV2r K3l K3r K11 K17 K34; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17 K34) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K3l K3r K11 K17 K34; lia | clear - HV2l HV2r K3l K3r K11 K17 K34; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17 K34) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K3l K3r K11 K17 K34; lia | clear - HV2l HV2r K3l K3r K11 K17 K34; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17 K34) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K3l K3r K11 K17 K34; lia | clear - HV2l HV2r K3l K3r K11 K17 K34; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17 K34) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K3l K3r K11 K17 K34; lia | clear - HV2l HV2r K3l K3r K11 K17 K34; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17 K34) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K3l K3r K11 K17 K34; lia | clear - HV2l HV2r K3l K3r K11 K17 K34; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K23l K23r K24 K25 K33 K34 K35 K36 HV34l HV34r K21l K21r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K19l K19r K23l K23r K24 K25 K33 K34 K35 K36 HV34l HV34r K21l K21r; lia | clear - HV33l HV33r K19l K19r K23l K23r K24 K25 K33 K34 K35 K36 HV34l HV34r K21l K21r; lia | clear - HV33l HV33r K19l K19r K23l K23r K24 K25 K33 K34 K35 K36 HV34l HV34r K21l K21r; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K23l K23r K24 K25 K33 K34 K35 K36 HV34l HV34r K21l K21r) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K23l K23r K24 K25 K33 K34 K35 K36 HV34l HV34r K21l K21r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17 K34) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K23l K23r K24 K25 K33 K34 K35 K36 HV34l HV34r K21l K21r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11 K18 K35) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K23l K23r K24 K25 K33 K34 K35 K36 HV34l HV34r K21l K21r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K13 K17 K18 K36) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K23l K23r K24 K25 K33 K34 K35 K36 HV34l HV34r K21l K21r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K19l K19r K23l K23r K24 K25 K33 K34 K35 K36 HV34l HV34r K21l K21r; lia | clear - HV33l HV33r K19l K19r K23l K23r K24 K25 K33 K34 K35 K36 HV34l HV34r K21l K21r; lia | clear - HV33l HV33r K19l K19r K23l K23r K24 K25 K33 K34 K35 K36 HV34l HV34r K21l K21r; lia | exactA K37]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaskB7.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaskB7.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((vz_33 + vz_34) + 0) <= bv_unsigned a < ((vz_33 + vz_34) + 0) + 1) -> ~ ((vz_10 + 8) <= bv_unsigned a < (vz_10 + 8) + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PaskB7.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K19l K19r K23l K23r K24 K25 K33 K34 K35 K36 HV34l HV34r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K19l K19r K23l K23r K24 K25 K33 K34 K35 K36 HV34l HV34r K21l K21r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV10l HV10r K6l K6r K8 K11 K18 K35) | evalEk' ZA Hag ltac:(clear) | clear - HV10l HV10r K6l K6r K8 K11 K18 K35 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaskB7.ps0) with 0xaf0f4 in Hms. change (SR.ps_regs PaskB7.ps0) with (map (fun i => (i, nth i PaskB7.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaskB7.ps0) with PaskB7.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaskB7.regs0 PaskB7.regs_out0 60 KS_askB7 KS_askB7_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaskB7.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaskB7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskB7.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaskB7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskB7.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaskB7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskB7.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PaskB7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskB7.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaskB7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskB7.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaskB7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskB7.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaskB7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskB7.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaskB7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskB7.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PaskB7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K6l K6r K8 K11 K18 K35) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K19l K19r K23l K23r K24 K25 K33 K34 K35 K36 HV34l HV34r K21l K21r) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K19l K19r K23l K23r K24 K25 K33 K34 K35 K36 HV34l HV34r K21l K21r) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K16l K16r) | byte_tac ltac:(clear - HV40l HV40r K16l K16r) | clear; lia].
Qed.

Module PaskBp := BndP_Ea_049S8.LibSegEa_askBp.
Definition KS_askBp : list nat := Eval vm_compute in (BG.kept_list 60 PaskBp.regs0 PaskBp.regs_out0).
Lemma KS_askBp_ok : BG.kept_ok 60 PaskBp.regs0 PaskBp.regs_out0 KS_askBp = true. Proof. vm_compute. reflexivity. Qed.
Lemma askBp_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + (V 34%nat)) -> getr R (reg 19) = Z_to_bv 64 ((((V 10%nat) + 8) / 8) + 2147450880) -> getr R (reg 20) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1253376 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487216 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 6914048 <= (V 10%nat) <= 140737488355304 -> aligned (V 10%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 10%nat) 24 -> (((V 2%nat) - 256) + 256 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 256)) ->
  4096 <= (V 36%nat) <= 140737488355327 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 1 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 1 -> L5.u8_at RSEGS M (V 36%nat) (V 40%nat) ->
  0 <= (V 40%nat) <= 255 -> ((V 36%nat) + 1 <= ((V 2%nat) - 256) \/ ((V 2%nat) - 256) + 256 <= (V 36%nat)) -> ((V 36%nat) + 1 <= (V 10%nat) \/ (V 10%nat) + 24 <= (V 36%nat)) -> 4096 <= (V 33%nat) <= 140737488355328 ->
  aligned (V 33%nat) 16 -> 0 <= (V 34%nat) <= 17179869184 -> 0 <= (V 35%nat) <= 17179869184 -> 4096 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + (V 35%nat) <= 2147446784) -> (65536 + 6848512 <= (V 33%nat) \/ (V 33%nat) + (V 35%nat) <= 65536) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) ->
  L5.writable RSEGS M ((V 33%nat) + (V 34%nat)) 1 -> (2147446784 + 17592186048512 <= ((V 33%nat) + (V 34%nat)) \/ ((V 33%nat) + (V 34%nat)) + 1 <= 2147446784) -> (((V 33%nat) + (V 34%nat)) + 1 <= ((V 2%nat) - 256) \/ ((V 2%nat) - 256) + 256 <= ((V 33%nat) + (V 34%nat))) -> (((V 33%nat) + (V 34%nat)) + 1 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 33%nat) + (V 34%nat))) ->
  (((V 33%nat) + (V 34%nat)) + 1 <= (V 36%nat) \/ (V 36%nat) + 1 <= ((V 33%nat) + (V 34%nat))) -> L5.u8_at RSEGS M ((((V 33%nat) + (V 34%nat)) / 8) + 2147450880) (((Z.land (V 34%nat) 7) + 1) mod 2 ^ 64) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((((V 33%nat) + (V 34%nat)) + 0) <= bv_unsigned a < (((V 33%nat) + (V 34%nat)) + 0) + 1) -> ~ (((V 10%nat) + 8) <= bv_unsigned a < ((V 10%nat) + 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((((V 33%nat) + (V 34%nat)) + 0) <= i < (((V 33%nat) + (V 34%nat)) + 0) + 1) -> ~ (((V 10%nat) + 8) <= i < ((V 10%nat) + 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xaf094 M) (st fx' R' 0xaf0f4 M')
        /\ (forall x, In x KS_askBp -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 33%nat) + (V 34%nat)) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ bv_unsigned (getr R' (reg 12)) = (Z.land (V 34%nat) 7)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 10%nat) + 8) (((V 33%nat) + (V 34%nat)) + 1)
        /\ L5.u8_at RSEGS M' ((V 33%nat) + (V 34%nat)) (V 40%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 G2 G8 G9 G10 G11 G12 G18 G19 G20 K0 K1 K2 pvzI17 K4 K5 pvzI18 K7 K8 K9 K10 K11 pvzI19 K13 K14 K15 pvzI20 K17 K18 pvzI21 K20 pvzI22 pvzI23 pvzI24 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV35l; move HV35l before pvzI5; pose proof (proj2 pvzI5) as HV35r; move HV35r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV36l; move HV36l before pvzI6; pose proof (proj2 pvzI6) as HV36r; move HV36r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV40l; move HV40l before pvzI7; pose proof (proj2 pvzI7) as HV40r; move HV40r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV44l; move HV44l before pvzI8; pose proof (proj2 pvzI8) as HV44r; move HV44r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV45l; move HV45l before pvzI9; pose proof (proj2 pvzI9) as HV45r; move HV45r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV46l; move HV46l before pvzI10; pose proof (proj2 pvzI10) as HV46r; move HV46r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV47l; move HV47l before pvzI11; pose proof (proj2 pvzI11) as HV47r; move HV47r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV48l; move HV48l before pvzI12; pose proof (proj2 pvzI12) as HV48r; move HV48r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV49l; move HV49l before pvzI13; pose proof (proj2 pvzI13) as HV49r; move HV49r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV55l; move HV55l before pvzI14; pose proof (proj2 pvzI14) as HV55r; move HV55r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV56l; move HV56l before pvzI15; pose proof (proj2 pvzI15) as HV56r; move HV56r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV57l; move HV57l before pvzI16; pose proof (proj2 pvzI16) as HV57r; move HV57r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K3l; move K3l before pvzI17; pose proof (proj2 pvzI17) as K3r; move K3r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K6l; move K6l before pvzI18; pose proof (proj2 pvzI18) as K6r; move K6r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K12l; move K12l before pvzI19; pose proof (proj2 pvzI19) as K12r; move K12r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K16l; move K16l before pvzI20; pose proof (proj2 pvzI20) as K16r; move K16r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K19l; move K19l before pvzI21; pose proof (proj2 pvzI21) as K19r; move K19r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K21l; move K21l before pvzI22; pose proof (proj2 pvzI22) as K21r; move K21r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K22l; move K22l before pvzI23; pose proof (proj2 pvzI23) as K22r; move K22r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K23l; move K23l before pvzI24; pose proof (proj2 pvzI24) as K23r; move K23r before pvzI24; clear pvzI24.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 40%nat => Z_to_bv 64 vz_40 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 40%nat => vz_40 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PaskBp.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaskBp.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaskBp.kn0).
  { unfold know_ok, PaskBp.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17 K34) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17 K34) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17 K34) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K17 K34; lia | clear - HV2l HV2r K3l K3r K11 K17 K34; lia | clear - HV2l HV2r K3l K3r K11 K17 K34; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11 K18 K35) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11 K18 K35) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11 K18 K35) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11 K18 K35) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K6l K6r K8 K11 K18 K35; lia | clear - HV10l HV10r K6l K6r K8 K11 K18 K35; lia | clear - HV10l HV10r K6l K6r K8 K11 K18 K35; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11 K18 K35) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K6l K6r K8 K11 K18 K35; lia | clear - HV10l HV10r K6l K6r K8 K11 K18 K35; lia | clear - HV10l HV10r K6l K6r K8 K11 K18 K35; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11 K18 K35) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K13 K17 K18 K36) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K13 K17 K18 K36) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K13 K17 K18 K36) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K12l K12r K13 K17 K18 K36; lia | clear - HV36l HV36r K12l K12r K13 K17 K18 K36; lia | clear - HV36l HV36r K12l K12r K13 K17 K18 K36; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K13 K17 K18 K36) | evalEk ZA ltac:(clear - HV40l HV40r K16l K16r) | clear - HV36l HV36r K12l K12r K13 K17 K18 K36; lia | clear - HV36l HV36r K12l K12r K13 K17 K18 K36; lia | byte_tac ltac:(clear - HV40l HV40r K16l K16r) | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K13 K17 K18 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17 K34) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K13 K17 K18 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11 K18 K35) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K23l K23r K24 K25 K33 K34 K35 K36) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K23l K23r K24 K25 K33 K34 K35 K36) | clear; lia | exact K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K21l K21r K33 K34 K35 K36) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K22l K22r K23l K23r K24 K25) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K23l K23r K24 K25 K33 K34 K35 K36 HV35l HV35r K22l K22r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K23l K23r K24 K25 K33 K34 K35 K36) | evalEk ZA ltac:(clear - HV35l HV35r K22l K22r K23l K23r K24 K25) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K23l K23r K24 K25 K33 K34 K35 K36) | evalEk ZA ltac:(clear - HV35l HV35r K22l K22r K23l K23r K24 K25) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17 K34) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K3l K3r K11 K17 K34; lia | clear - HV2l HV2r K3l K3r K11 K17 K34; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17 K34) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K3l K3r K11 K17 K34; lia | clear - HV2l HV2r K3l K3r K11 K17 K34; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17 K34) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K3l K3r K11 K17 K34; lia | clear - HV2l HV2r K3l K3r K11 K17 K34; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17 K34) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K3l K3r K11 K17 K34; lia | clear - HV2l HV2r K3l K3r K11 K17 K34; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17 K34) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K3l K3r K11 K17 K34; lia | clear - HV2l HV2r K3l K3r K11 K17 K34; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17 K34) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K3l K3r K11 K17 K34; lia | clear - HV2l HV2r K3l K3r K11 K17 K34; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K23l K23r K24 K25 K33 K34 K35 K36 HV34l HV34r K21l K21r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K19l K19r K23l K23r K24 K25 K33 K34 K35 K36 HV34l HV34r K21l K21r; lia | clear - HV33l HV33r K19l K19r K23l K23r K24 K25 K33 K34 K35 K36 HV34l HV34r K21l K21r; lia | clear - HV33l HV33r K19l K19r K23l K23r K24 K25 K33 K34 K35 K36 HV34l HV34r K21l K21r; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K23l K23r K24 K25 K33 K34 K35 K36 HV34l HV34r K21l K21r) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K23l K23r K24 K25 K33 K34 K35 K36 HV34l HV34r K21l K21r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17 K34) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K23l K23r K24 K25 K33 K34 K35 K36 HV34l HV34r K21l K21r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11 K18 K35) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K23l K23r K24 K25 K33 K34 K35 K36 HV34l HV34r K21l K21r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K13 K17 K18 K36) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K23l K23r K24 K25 K33 K34 K35 K36 HV34l HV34r K21l K21r) | ((L5K.evalB ZA; pvz_unfold ZA); reflexivity) | clear - HV33l HV33r K19l K19r K23l K23r K24 K25 K33 K34 K35 K36 HV34l HV34r K21l K21r; lia | clear - HV33l HV33r K19l K19r K23l K23r K24 K25 K33 K34 K35 K36 HV34l HV34r K21l K21r; lia | byte_tac ltac:(clear - HV34l HV34r K21l K21r K33 K34 K35 K36) | exactA K37]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaskBp.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaskBp.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((vz_33 + vz_34) + 0) <= bv_unsigned a < ((vz_33 + vz_34) + 0) + 1) -> ~ ((vz_10 + 8) <= bv_unsigned a < (vz_10 + 8) + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PaskBp.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K19l K19r K23l K23r K24 K25 K33 K34 K35 K36 HV34l HV34r K21l K21r) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K19l K19r K23l K23r K24 K25 K33 K34 K35 K36 HV34l HV34r K21l K21r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV10l HV10r K6l K6r K8 K11 K18 K35) | evalEk' ZA Hag ltac:(clear) | clear - HV10l HV10r K6l K6r K8 K11 K18 K35 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaskBp.ps0) with 0xaf0f4 in Hms. change (SR.ps_regs PaskBp.ps0) with (map (fun i => (i, nth i PaskBp.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaskBp.ps0) with PaskBp.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaskBp.regs0 PaskBp.regs_out0 60 KS_askBp KS_askBp_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaskBp.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaskBp.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskBp.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaskBp.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskBp.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaskBp.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskBp.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PaskBp.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskBp.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaskBp.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskBp.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaskBp.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskBp.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PaskBp.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
  split. { rewrite (BG.out_reg PaskBp.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaskBp.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskBp.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaskBp.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskBp.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PaskBp.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K6l K6r K8 K11 K18 K35) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K19l K19r K23l K23r K24 K25 K33 K34 K35 K36 HV34l HV34r K21l K21r) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K19l K19r K23l K23r K24 K25 K33 K34 K35 K36 HV34l HV34r K21l K21r) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K16l K16r) | byte_tac ltac:(clear - HV40l HV40r K16l K16r) | clear; lia].
Qed.

Module PaskR := BndP_Ea_049S8.LibSegEa_askR.
Definition KS_askR : list nat := Eval vm_compute in (BG.kept_list 60 PaskR.regs0 PaskR.regs_out0).
Lemma KS_askR_ok : BG.kept_ok 60 PaskR.regs0 PaskR.regs_out0 KS_askR = true. Proof. vm_compute. reflexivity. Qed.
Lemma askR_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 (V 41%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + (V 34%nat)) -> getr R (reg 19) = Z_to_bv 64 ((((V 10%nat) + 8) / 8) + 2147450880) -> getr R (reg 20) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1253376 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487216 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 6914048 <= (V 10%nat) <= 140737488355304 -> aligned (V 10%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 10%nat) 24 -> (((V 2%nat) - 256) + 256 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 256)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 10%nat) + 8) <= bv_unsigned a < ((V 10%nat) + 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 10%nat) + 8) <= i < ((V 10%nat) + 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xaf0cc M) (st fx' R' 0xaf0f4 M')
        /\ (forall x, In x KS_askR -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 10%nat) + 8) (V 41%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 G2 G8 G9 G10 G11 G12 G18 G19 G20 K0 K1 K2 pvzI15 K4 K5 pvzI16 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV41l; move HV41l before pvzI6; pose proof (proj2 pvzI6) as HV41r; move HV41r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV44l; move HV44l before pvzI7; pose proof (proj2 pvzI7) as HV44r; move HV44r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV45l; move HV45l before pvzI8; pose proof (proj2 pvzI8) as HV45r; move HV45r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV46l; move HV46l before pvzI9; pose proof (proj2 pvzI9) as HV46r; move HV46r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV47l; move HV47l before pvzI10; pose proof (proj2 pvzI10) as HV47r; move HV47r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV48l; move HV48l before pvzI11; pose proof (proj2 pvzI11) as HV48r; move HV48r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV49l; move HV49l before pvzI12; pose proof (proj2 pvzI12) as HV49r; move HV49r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV56l; move HV56l before pvzI13; pose proof (proj2 pvzI13) as HV56r; move HV56r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV57l; move HV57l before pvzI14; pose proof (proj2 pvzI14) as HV57r; move HV57r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K3l; move K3l before pvzI15; pose proof (proj2 pvzI15) as K3r; move K3r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K6l; move K6l before pvzI16; pose proof (proj2 pvzI16) as K6r; move K6r before pvzI16; clear pvzI16.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 41%nat => Z_to_bv 64 vz_41 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 41%nat => vz_41 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PaskR.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaskR.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaskR.kn0).
  { unfold know_ok, PaskR.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K17]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaskR.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaskR.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_10 + 8) <= bv_unsigned a < (vz_10 + 8) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PaskR.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV10l HV10r K6l K6r K8 K11) | evalEk' ZA Hag ltac:(clear) | clear - HV10l HV10r K6l K6r K8 K11 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaskR.ps0) with 0xaf0f4 in Hms. change (SR.ps_regs PaskR.ps0) with (map (fun i => (i, nth i PaskR.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaskR.ps0) with PaskR.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaskR.regs0 PaskR.regs_out0 60 KS_askR KS_askR_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaskR.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaskR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskR.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaskR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskR.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaskR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskR.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PaskR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskR.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaskR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskR.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaskR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskR.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaskR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskR.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PaskR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K6l K6r K8 K11) | evalEk' ZA Hag ltac:(clear - HV41l HV41r) | clear; lia].
Qed.

Module PaskS1z := BndP_Ea_049S8.LibSegEa_askS1z.
Definition KS_askS1z : list nat := Eval vm_compute in (BG.kept_list 60 PaskS1z.regs0 PaskS1z.regs_out0).
Lemma KS_askS1z_ok : BG.kept_ok 60 PaskS1z.regs0 PaskS1z.regs_out0 KS_askS1z = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma askS1z_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 717004 -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 ((bv_unsigned (getr R (reg 10))) + 8) -> getr R (reg 9) = Z_to_bv 64 (bv_unsigned (getr R (reg 11))) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 0 -> getr R (reg 19) = Z_to_bv 64 ((((bv_unsigned (getr R (reg 10))) + 8) / 8) + 2147450880) -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 (V 50%nat) -> getr R (reg 22) = Z_to_bv 64 (V 51%nat) ->
  L5.img_clear M 1253376 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 -> 6914048 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> (2147446784 + 17592186048512 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= 2147446784) -> L5KA.zeros_at M (((bv_unsigned (getr R (reg 10))) / 8) + 2147450880) 3 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 ->
  (((V 2%nat) - 256) + 256 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= ((V 2%nat) - 256)) -> 4096 <= (bv_unsigned (getr R (reg 11))) <= 140737488355327 -> (2147446784 + 17592186048512 <= (bv_unsigned (getr R (reg 11))) \/ (bv_unsigned (getr R (reg 11))) + 1 <= 2147446784) -> L5KA.zeros_at M (((bv_unsigned (getr R (reg 11))) / 8) + 2147450880) 1 ->
  L5.u8_at RSEGS M (bv_unsigned (getr R (reg 11))) (V 40%nat) -> 0 <= (V 40%nat) <= 255 -> ((bv_unsigned (getr R (reg 11))) + 1 <= ((V 2%nat) - 256) \/ ((V 2%nat) - 256) + 256 <= (bv_unsigned (getr R (reg 11)))) -> ((bv_unsigned (getr R (reg 11))) + 1 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= (bv_unsigned (getr R (reg 11)))) ->
  L5.u64_at RSEGS M (bv_unsigned (getr R (reg 10))) 0 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) 0 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 16) 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 160) <= bv_unsigned a < ((V 2%nat) - 160) + 112) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 160) <= i < ((V 2%nat) - 160) + 112) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xaf130 M) (st fx' R' 0x131ec0 M')
        /\ (forall x, In x KS_askS1z -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 717288
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 160)
        /\ getr R' (reg 9) = getr R (reg 10)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 18446744073709551615
        /\ getr R' (reg 12) = Z_to_bv 64 4611686018427387903
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 18) = getr R (reg 11)
        /\ getr R' (reg 19) = Z_to_bv 64 1
        /\ getr R' (reg 20) = Z_to_bv 64 ((((bv_unsigned (getr R (reg 10))) + 8) / 8) + 2147450880)
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ getr R' (reg 22) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (bv_unsigned (getr R (reg 10)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 51%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) ((((bv_unsigned (getr R (reg 10))) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 11)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) ((bv_unsigned (getr R (reg 10))) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) 717004).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G1 G2 G8 G9 G12 G18 G19 G20 G21 G22 K0 K1 K2 pvzI6 K4 K5 K6 pvzI7 K8 K9 K10 K11 K12 pvzI8 K14 K15 K16 pvzI9 K18 K19 K20 K21 K22.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV40l; move HV40l before pvzI2; pose proof (proj2 pvzI2) as HV40r; move HV40r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV50l; move HV50l before pvzI3; pose proof (proj2 pvzI3) as HV50r; move HV50r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV51l; move HV51l before pvzI4; pose proof (proj2 pvzI4) as HV51r; move HV51r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV57l; move HV57l before pvzI5; pose proof (proj2 pvzI5) as HV57r; move HV57r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K7l; move K7l before pvzI7; pose proof (proj2 pvzI7) as K7r; move K7r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K13l; move K13l before pvzI8; pose proof (proj2 pvzI8) as K13r; move K13r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K17l; move K17l before pvzI9; pose proof (proj2 pvzI9) as K17r; move K17r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 40%nat => Z_to_bv 64 vz_40 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 40%nat => vz_40 | 50%nat => vz_50 | 51%nat => vz_51 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PaskS1z.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaskS1z.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaskS1z.kn0).
  { unfold know_ok, PaskS1z.kn0.
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
  pvz_hg ltac:(idtac; destruct (PaskS1z.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaskS1z.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 160) <= bv_unsigned a < (vz_2 - 160) + 112) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PaskS1z.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaskS1z.ps0) with 0x131ec0 in Hms. change (SR.ps_regs PaskS1z.ps0) with (map (fun i => (i, nth i PaskS1z.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaskS1z.ps0) with PaskS1z.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaskS1z.regs0 PaskS1z.regs_out0 60 KS_askS1z KS_askS1z_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaskS1z.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaskS1z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS1z.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaskS1z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS1z.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PaskS1z.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PaskS1z.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaskS1z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS1z.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaskS1z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS1z.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PaskS1z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS1z.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PaskS1z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS1z.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaskS1z.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PaskS1z.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaskS1z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS1z.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PaskS1z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS1z.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PaskS1z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS1z.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PaskS1z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - K7l K7r K9 K12 K19) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - HV51l HV51r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - HV50l HV50r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - K7l K7r K9 K12 K19) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - K13l K13r K14 K18 K19) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - K7l K7r K9 K12 K19) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PaskS1o := BndP_Ea_049S8.LibSegEa_askS1o.
Definition KS_askS1o : list nat := Eval vm_compute in (BG.kept_list 60 PaskS1o.regs0 PaskS1o.regs_out0).
Lemma KS_askS1o_ok : BG.kept_ok 60 PaskS1o.regs0 PaskS1o.regs_out0 KS_askS1o = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma askS1o_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 717004 -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 ((bv_unsigned (getr R (reg 10))) + 8) -> getr R (reg 9) = Z_to_bv 64 (bv_unsigned (getr R (reg 11))) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + 1) -> getr R (reg 19) = Z_to_bv 64 ((((bv_unsigned (getr R (reg 10))) + 8) / 8) + 2147450880) -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 (V 50%nat) -> getr R (reg 22) = Z_to_bv 64 (V 51%nat) ->
  L5.img_clear M 1253376 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 -> 6914048 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> (2147446784 + 17592186048512 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= 2147446784) -> L5KA.zeros_at M (((bv_unsigned (getr R (reg 10))) / 8) + 2147450880) 3 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 ->
  (((V 2%nat) - 256) + 256 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= ((V 2%nat) - 256)) -> 4096 <= (bv_unsigned (getr R (reg 11))) <= 140737488355327 -> (2147446784 + 17592186048512 <= (bv_unsigned (getr R (reg 11))) \/ (bv_unsigned (getr R (reg 11))) + 1 <= 2147446784) -> L5KA.zeros_at M (((bv_unsigned (getr R (reg 11))) / 8) + 2147450880) 1 ->
  L5.u8_at RSEGS M (bv_unsigned (getr R (reg 11))) (V 40%nat) -> 0 <= (V 40%nat) <= 255 -> ((bv_unsigned (getr R (reg 11))) + 1 <= ((V 2%nat) - 256) \/ ((V 2%nat) - 256) + 256 <= (bv_unsigned (getr R (reg 11)))) -> ((bv_unsigned (getr R (reg 11))) + 1 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= (bv_unsigned (getr R (reg 11)))) ->
  L5.u64_at RSEGS M (bv_unsigned (getr R (reg 10))) (V 33%nat) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) ((V 33%nat) + 1) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 16) ((V 33%nat) + 1) -> 4096 <= (V 33%nat) <= 140737488355327 ->
  aligned (V 33%nat) 16 -> (65536 + 6848512 <= (V 33%nat) \/ (V 33%nat) + 1 <= 65536) -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 1 <= 2147446784) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 160) <= bv_unsigned a < ((V 2%nat) - 160) + 112) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 160) <= i < ((V 2%nat) - 160) + 112) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xaf130 M) (st fx' R' 0x131ec0 M')
        /\ (forall x, In x KS_askS1o -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 717288
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 160)
        /\ getr R' (reg 9) = getr R (reg 10)
        /\ getr R' (reg 10) = Z_to_bv 64 2
        /\ getr R' (reg 11) = Z_to_bv 64 18446744073709551615
        /\ getr R' (reg 12) = Z_to_bv 64 4611686018427387903
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 18) = getr R (reg 11)
        /\ getr R' (reg 19) = Z_to_bv 64 2
        /\ getr R' (reg 20) = Z_to_bv 64 ((((bv_unsigned (getr R (reg 10))) + 8) / 8) + 2147450880)
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ getr R' (reg 22) = Z_to_bv 64 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (bv_unsigned (getr R (reg 10)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 51%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) ((((bv_unsigned (getr R (reg 10))) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 33%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 11)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) ((bv_unsigned (getr R (reg 10))) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) 717004).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G1 G2 G8 G9 G12 G18 G19 G20 G21 G22 K0 K1 K2 pvzI7 K4 K5 K6 pvzI8 K8 K9 K10 K11 K12 pvzI9 K14 K15 K16 pvzI10 K18 K19 K20 K21 K22 pvzI11 K24 K25 K26.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV40l; move HV40l before pvzI3; pose proof (proj2 pvzI3) as HV40r; move HV40r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV50l; move HV50l before pvzI4; pose proof (proj2 pvzI4) as HV50r; move HV50r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV51l; move HV51l before pvzI5; pose proof (proj2 pvzI5) as HV51r; move HV51r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV57l; move HV57l before pvzI6; pose proof (proj2 pvzI6) as HV57r; move HV57r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K7l; move K7l before pvzI8; pose proof (proj2 pvzI8) as K7r; move K7r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K13l; move K13l before pvzI9; pose proof (proj2 pvzI9) as K13r; move K13r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K17l; move K17l before pvzI10; pose proof (proj2 pvzI10) as K17r; move K17r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K23l; move K23l before pvzI11; pose proof (proj2 pvzI11) as K23r; move K23r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 40%nat => Z_to_bv 64 vz_40 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 40%nat => vz_40 | 50%nat => vz_50 | 51%nat => vz_51 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PaskS1o.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaskS1o.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaskS1o.kn0).
  { unfold know_ok, PaskS1o.kn0.
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
  pvz_hg ltac:(idtac; destruct (PaskS1o.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaskS1o.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 160) <= bv_unsigned a < (vz_2 - 160) + 112) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PaskS1o.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaskS1o.ps0) with 0x131ec0 in Hms. change (SR.ps_regs PaskS1o.ps0) with (map (fun i => (i, nth i PaskS1o.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaskS1o.ps0) with PaskS1o.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaskS1o.regs0 PaskS1o.regs_out0 60 KS_askS1o KS_askS1o_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaskS1o.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaskS1o.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS1o.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaskS1o.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS1o.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PaskS1o.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PaskS1o.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaskS1o.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS1o.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaskS1o.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS1o.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PaskS1o.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS1o.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PaskS1o.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS1o.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaskS1o.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PaskS1o.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaskS1o.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS1o.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PaskS1o.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS1o.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PaskS1o.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS1o.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PaskS1o.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - K7l K7r K9 K12 K19) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - HV51l HV51r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - HV50l HV50r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - K7l K7r K9 K12 K19) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K23l K23r K25 K26) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - K13l K13r K14 K18 K19) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - K7l K7r K9 K12 K19) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PaskS1 := BndP_Ea_049S8.LibSegEa_askS1.
Definition KS_askS1 : list nat := Eval vm_compute in (BG.kept_list 60 PaskS1.regs0 PaskS1.regs_out0).
Lemma KS_askS1_ok : BG.kept_ok 60 PaskS1.regs0 PaskS1.regs_out0 KS_askS1 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma askS1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 717004 -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 ((bv_unsigned (getr R (reg 10))) + 8) -> getr R (reg 9) = Z_to_bv 64 (bv_unsigned (getr R (reg 11))) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 19) = Z_to_bv 64 ((((bv_unsigned (getr R (reg 10))) + 8) / 8) + 2147450880) -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 (V 50%nat) -> getr R (reg 22) = Z_to_bv 64 (V 51%nat) ->
  L5.img_clear M 1253376 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 -> 6914048 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> (2147446784 + 17592186048512 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= 2147446784) -> L5KA.zeros_at M (((bv_unsigned (getr R (reg 10))) / 8) + 2147450880) 3 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 ->
  (((V 2%nat) - 256) + 256 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= ((V 2%nat) - 256)) -> 4096 <= (bv_unsigned (getr R (reg 11))) <= 140737488355327 -> (2147446784 + 17592186048512 <= (bv_unsigned (getr R (reg 11))) \/ (bv_unsigned (getr R (reg 11))) + 1 <= 2147446784) -> L5KA.zeros_at M (((bv_unsigned (getr R (reg 11))) / 8) + 2147450880) 1 ->
  L5.u8_at RSEGS M (bv_unsigned (getr R (reg 11))) (V 40%nat) -> 0 <= (V 40%nat) <= 255 -> ((bv_unsigned (getr R (reg 11))) + 1 <= ((V 2%nat) - 256) \/ ((V 2%nat) - 256) + 256 <= (bv_unsigned (getr R (reg 11)))) -> ((bv_unsigned (getr R (reg 11))) + 1 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= (bv_unsigned (getr R (reg 11)))) ->
  L5.u64_at RSEGS M (bv_unsigned (getr R (reg 10))) (V 33%nat) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) ((V 33%nat) + (V 35%nat)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 16) ((V 33%nat) + (V 35%nat)) -> 4096 <= (V 33%nat) <= 140737488355328 ->
  aligned (V 33%nat) 16 -> 0 <= (V 34%nat) <= 17179869184 -> 2 <= (V 35%nat) <= 8589934592 -> 4096 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + (V 35%nat) <= 2147446784) -> (65536 + 6848512 <= (V 33%nat) \/ (V 33%nat) + (V 35%nat) <= 65536) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 160) <= bv_unsigned a < ((V 2%nat) - 160) + 112) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 160) <= i < ((V 2%nat) - 160) + 112) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xaf130 M) (st fx' R' 0x131ec0 M')
        /\ (forall x, In x KS_askS1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 717288
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 160)
        /\ getr R' (reg 9) = getr R (reg 10)
        /\ getr R' (reg 10) = Z_to_bv 64 (2 * (V 35%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 18446744073709551615
        /\ getr R' (reg 12) = Z_to_bv 64 4611686018427387903
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 18) = getr R (reg 11)
        /\ getr R' (reg 19) = Z_to_bv 64 (2 * (V 35%nat))
        /\ getr R' (reg 20) = Z_to_bv 64 ((((bv_unsigned (getr R (reg 10))) + 8) / 8) + 2147450880)
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ getr R' (reg 22) = Z_to_bv 64 (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (bv_unsigned (getr R (reg 10)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 51%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) ((((bv_unsigned (getr R (reg 10))) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 33%nat) + (V 35%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 11)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) ((bv_unsigned (getr R (reg 10))) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) 717004).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G1 G2 G8 G9 G12 G18 G19 G20 G21 G22 K0 K1 K2 pvzI9 K4 K5 K6 pvzI10 K8 K9 K10 K11 K12 pvzI11 K14 K15 K16 pvzI12 K18 K19 K20 K21 K22 pvzI13 K24 pvzI14 pvzI15 pvzI16 K28 K29.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV40l; move HV40l before pvzI5; pose proof (proj2 pvzI5) as HV40r; move HV40r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV50l; move HV50l before pvzI6; pose proof (proj2 pvzI6) as HV50r; move HV50r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV51l; move HV51l before pvzI7; pose proof (proj2 pvzI7) as HV51r; move HV51r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV57l; move HV57l before pvzI8; pose proof (proj2 pvzI8) as HV57r; move HV57r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K7l; move K7l before pvzI10; pose proof (proj2 pvzI10) as K7r; move K7r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K13l; move K13l before pvzI11; pose proof (proj2 pvzI11) as K13r; move K13r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K17l; move K17l before pvzI12; pose proof (proj2 pvzI12) as K17r; move K17r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K23l; move K23l before pvzI13; pose proof (proj2 pvzI13) as K23r; move K23r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K25l; move K25l before pvzI14; pose proof (proj2 pvzI14) as K25r; move K25r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K26l; move K26l before pvzI15; pose proof (proj2 pvzI15) as K26r; move K26r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K27l; move K27l before pvzI16; pose proof (proj2 pvzI16) as K27r; move K27r before pvzI16; clear pvzI16.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 40%nat => Z_to_bv 64 vz_40 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 40%nat => vz_40 | 50%nat => vz_50 | 51%nat => vz_51 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PaskS1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaskS1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaskS1.kn0).
  { unfold know_ok, PaskS1.kn0.
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
  pvz_hg ltac:(idtac; destruct (PaskS1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaskS1.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 160) <= bv_unsigned a < (vz_2 - 160) + 112) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PaskS1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaskS1.ps0) with 0x131ec0 in Hms. change (SR.ps_regs PaskS1.ps0) with (map (fun i => (i, nth i PaskS1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaskS1.ps0) with PaskS1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaskS1.regs0 PaskS1.regs_out0 60 KS_askS1 KS_askS1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaskS1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaskS1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS1.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaskS1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS1.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PaskS1.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PaskS1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaskS1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaskS1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PaskS1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS1.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PaskS1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS1.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaskS1.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PaskS1.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaskS1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS1.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PaskS1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS1.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PaskS1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS1.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PaskS1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - K7l K7r K9 K12 K19) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - HV51l HV51r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - HV50l HV50r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - K7l K7r K9 K12 K19) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K23l K23r K27l K27r K28 K29 HV35l HV35r K26l K26r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - K13l K13r K14 K18 K19) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear - K7l K7r K9 K12 K19) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PaskS2z := BndP_Ea_049S8.LibSegEa_askS2z.
Definition KS_askS2z : list nat := Eval vm_compute in (BG.kept_list 60 PaskS2z.regs0 PaskS2z.regs_out0).
Lemma KS_askS2z_ok : BG.kept_ok 60 PaskS2z.regs0 PaskS2z.regs_out0 KS_askS2z = true. Proof. vm_compute. reflexivity. Qed.
Lemma askS2z_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 9) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 37%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 1 -> getr R (reg 20) = Z_to_bv 64 ((((V 10%nat) + 8) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 0 ->
  L5.img_clear M 1253376 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 -> 6914048 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 10%nat) 24 ->
  (((V 2%nat) - 256) + 256 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 256)) -> 4096 <= (V 36%nat) <= 140737488355327 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 1 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 1 ->
  L5.u8_at RSEGS M (V 36%nat) (V 40%nat) -> 0 <= (V 40%nat) <= 255 -> ((V 36%nat) + 1 <= ((V 2%nat) - 256) \/ ((V 2%nat) - 256) + 256 <= (V 36%nat)) -> ((V 36%nat) + 1 <= (V 10%nat) \/ (V 10%nat) + 24 <= (V 36%nat)) ->
  4096 <= (V 37%nat) <= 140737488355328 -> aligned (V 37%nat) 16 -> 4096 <= ((V 37%nat) + 1) <= 140737488355328 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 1 <= 2147446784) ->
  (65536 + 6848512 <= (V 37%nat) \/ (V 37%nat) + 1 <= 65536) -> L5.writable RSEGS M (V 37%nat) 1 -> (((V 2%nat) - 256) + 256 <= (V 37%nat) \/ (V 37%nat) + 1 <= ((V 2%nat) - 256)) -> ((V 10%nat) + 24 <= (V 37%nat) \/ (V 37%nat) + 1 <= (V 10%nat)) ->
  ((V 36%nat) + 1 <= (V 37%nat) \/ (V 37%nat) + 1 <= (V 36%nat)) -> L5.u8_at RSEGS M (((V 37%nat) / 8) + 2147450880) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 152) <= bv_unsigned a < ((V 2%nat) - 152) + 32) -> ~ (((V 37%nat) + 0) <= bv_unsigned a < ((V 37%nat) + 0) + 1) -> ~ (((V 2%nat) - 208) <= bv_unsigned a < ((V 2%nat) - 208) + 48) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 152) <= i < ((V 2%nat) - 152) + 32) -> ~ (((V 37%nat) + 0) <= i < ((V 37%nat) + 0) + 1) -> ~ (((V 2%nat) - 208) <= i < ((V 2%nat) - 208) + 48) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xaf1e8 M) (st fx' R' 0xaa6ec M')
        /\ (forall x, In x KS_askS2z -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 717796
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 208)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 152)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 10%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1317368
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 19) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) ((V 37%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) (V 10%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) ((V 10%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) 717380
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) ((V 37%nat) + 1)
        /\ L5.u8_at RSEGS M' (V 37%nat) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 37%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 37%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G22 K0 K1 K2 pvzI8 K4 K5 K6 pvzI9 K8 K9 K10 K11 K12 pvzI10 K14 K15 K16 pvzI11 K18 K19 pvzI12 K21 pvzI13 K23 K24 K25 K26 K27 K28 K29.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV40l; move HV40l before pvzI5; pose proof (proj2 pvzI5) as HV40r; move HV40r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV56l; move HV56l before pvzI6; pose proof (proj2 pvzI6) as HV56r; move HV56r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV57l; move HV57l before pvzI7; pose proof (proj2 pvzI7) as HV57r; move HV57r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K7l; move K7l before pvzI9; pose proof (proj2 pvzI9) as K7r; move K7r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K13l; move K13l before pvzI10; pose proof (proj2 pvzI10) as K13r; move K13r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K17l; move K17l before pvzI11; pose proof (proj2 pvzI11) as K17r; move K17r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K20l; move K20l before pvzI12; pose proof (proj2 pvzI12) as K20r; move K20r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K22l; move K22l before pvzI13; pose proof (proj2 pvzI13) as K22r; move K22r before pvzI13; clear pvzI13.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 40%nat => Z_to_bv 64 vz_40 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 36%nat => vz_36 | 37%nat => vz_37 | 40%nat => vz_40 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PaskS2z.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaskS2z.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaskS2z.kn0).
  { unfold know_ok, PaskS2z.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28; lia | clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28; lia | byte_tac ltac:(clear) | exactA K29]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaskS2z.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaskS2z.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 152) <= bv_unsigned a < (vz_2 - 152) + 32) -> ~ ((vz_37 + 0) <= bv_unsigned a < (vz_37 + 0) + 1) -> ~ ((vz_2 - 208) <= bv_unsigned a < (vz_2 - 208) + 48) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PaskS2z.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18 K26 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk' ZA Hag ltac:(clear) | clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18 K26 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaskS2z.ps0) with 0xaa6ec in Hms. change (SR.ps_regs PaskS2z.ps0) with (map (fun i => (i, nth i PaskS2z.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaskS2z.ps0) with PaskS2z.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaskS2z.regs0 PaskS2z.regs_out0 60 KS_askS2z KS_askS2z_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaskS2z.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaskS2z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS2z.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaskS2z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS2z.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaskS2z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS2z.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaskS2z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS2z.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaskS2z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS2z.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PaskS2z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS2z.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PaskS2z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS2z.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaskS2z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K28) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K17l K17r) | byte_tac ltac:(clear - HV40l HV40r K17l K17r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | clear; lia].
Qed.

Module PaskS2o := BndP_Ea_049S8.LibSegEa_askS2o.
Definition KS_askS2o : list nat := Eval vm_compute in (BG.kept_list 60 PaskS2o.regs0 PaskS2o.regs_out0).
Lemma KS_askS2o_ok : BG.kept_ok 60 PaskS2o.regs0 PaskS2o.regs_out0 KS_askS2o = true. Proof. vm_compute. reflexivity. Qed.
Lemma askS2o_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 9) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 37%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 2 -> getr R (reg 20) = Z_to_bv 64 ((((V 10%nat) + 8) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 1 ->
  L5.img_clear M 1253376 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 -> 6914048 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 10%nat) 24 ->
  (((V 2%nat) - 256) + 256 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 256)) -> 4096 <= (V 36%nat) <= 140737488355327 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 1 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 1 ->
  L5.u8_at RSEGS M (V 36%nat) (V 40%nat) -> 0 <= (V 40%nat) <= 255 -> ((V 36%nat) + 1 <= ((V 2%nat) - 256) \/ ((V 2%nat) - 256) + 256 <= (V 36%nat)) -> ((V 36%nat) + 1 <= (V 10%nat) \/ (V 10%nat) + 24 <= (V 36%nat)) ->
  4096 <= (V 37%nat) <= 140737488355328 -> aligned (V 37%nat) 16 -> 4096 <= ((V 37%nat) + 2) <= 140737488355328 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 2 <= 2147446784) ->
  (65536 + 6848512 <= (V 37%nat) \/ (V 37%nat) + 2 <= 65536) -> L5.writable RSEGS M (V 37%nat) 2 -> (((V 2%nat) - 256) + 256 <= (V 37%nat) \/ (V 37%nat) + 2 <= ((V 2%nat) - 256)) -> ((V 10%nat) + 24 <= (V 37%nat) \/ (V 37%nat) + 2 <= (V 10%nat)) ->
  ((V 36%nat) + 1 <= (V 37%nat) \/ (V 37%nat) + 2 <= (V 36%nat)) -> L5.u8_at RSEGS M ((((V 37%nat) + 1) / 8) + 2147450880) 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 152) <= bv_unsigned a < ((V 2%nat) - 152) + 32) -> ~ (((V 37%nat) + 1) <= bv_unsigned a < ((V 37%nat) + 1) + 1) -> ~ (((V 2%nat) - 208) <= bv_unsigned a < ((V 2%nat) - 208) + 48) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 152) <= i < ((V 2%nat) - 152) + 32) -> ~ (((V 37%nat) + 1) <= i < ((V 37%nat) + 1) + 1) -> ~ (((V 2%nat) - 208) <= i < ((V 2%nat) - 208) + 48) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xaf1e8 M) (st fx' R' 0xaa6ec M')
        /\ (forall x, In x KS_askS2o -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 717796
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 208)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 152)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 10%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1317368
        /\ getr R' (reg 12) = Z_to_bv 64 2
        /\ getr R' (reg 13) = Z_to_bv 64 1
        /\ getr R' (reg 19) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) ((V 37%nat) + 2)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) (V 10%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) ((V 10%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) 717380
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) ((V 37%nat) + 2)
        /\ L5.u8_at RSEGS M' ((V 37%nat) + 1) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 37%nat) + 2)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) ((V 37%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 37%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G22 K0 K1 K2 pvzI8 K4 K5 K6 pvzI9 K8 K9 K10 K11 K12 pvzI10 K14 K15 K16 pvzI11 K18 K19 pvzI12 K21 pvzI13 K23 K24 K25 K26 K27 K28 K29.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV40l; move HV40l before pvzI5; pose proof (proj2 pvzI5) as HV40r; move HV40r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV56l; move HV56l before pvzI6; pose proof (proj2 pvzI6) as HV56r; move HV56r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV57l; move HV57l before pvzI7; pose proof (proj2 pvzI7) as HV57r; move HV57r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K7l; move K7l before pvzI9; pose proof (proj2 pvzI9) as K7r; move K7r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K13l; move K13l before pvzI10; pose proof (proj2 pvzI10) as K13r; move K13r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K17l; move K17l before pvzI11; pose proof (proj2 pvzI11) as K17r; move K17r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K20l; move K20l before pvzI12; pose proof (proj2 pvzI12) as K20r; move K20r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K22l; move K22l before pvzI13; pose proof (proj2 pvzI13) as K22r; move K22r before pvzI13; clear pvzI13.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 40%nat => Z_to_bv 64 vz_40 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 36%nat => vz_36 | 37%nat => vz_37 | 40%nat => vz_40 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PaskS2o.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaskS2o.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaskS2o.kn0).
  { unfold know_ok, PaskS2o.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28; lia | clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28; lia | byte_tac ltac:(clear) | exactA K29]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaskS2o.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaskS2o.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 152) <= bv_unsigned a < (vz_2 - 152) + 32) -> ~ ((vz_37 + 1) <= bv_unsigned a < (vz_37 + 1) + 1) -> ~ ((vz_2 - 208) <= bv_unsigned a < (vz_2 - 208) + 48) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PaskS2o.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18 K26 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk' ZA Hag ltac:(clear) | clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18 K26 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaskS2o.ps0) with 0xaa6ec in Hms. change (SR.ps_regs PaskS2o.ps0) with (map (fun i => (i, nth i PaskS2o.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaskS2o.ps0) with PaskS2o.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaskS2o.regs0 PaskS2o.regs_out0 60 KS_askS2o KS_askS2o_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaskS2o.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaskS2o.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS2o.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaskS2o.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS2o.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaskS2o.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS2o.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaskS2o.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS2o.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaskS2o.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS2o.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PaskS2o.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS2o.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PaskS2o.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS2o.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaskS2o.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K28) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K17l K17r) | byte_tac ltac:(clear - HV40l HV40r K17l K17r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | clear; lia].
Qed.

Module PaskS2t := BndP_Ea_049S8.LibSegEa_askS2t.
Definition KS_askS2t : list nat := Eval vm_compute in (BG.kept_list 60 PaskS2t.regs0 PaskS2t.regs_out0).
Lemma KS_askS2t_ok : BG.kept_ok 60 PaskS2t.regs0 PaskS2t.regs_out0 KS_askS2t = true. Proof. vm_compute. reflexivity. Qed.
Lemma askS2t_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 9) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 37%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 4 -> getr R (reg 20) = Z_to_bv 64 ((((V 10%nat) + 8) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 2 ->
  L5.img_clear M 1253376 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 -> 6914048 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 10%nat) 24 ->
  (((V 2%nat) - 256) + 256 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 256)) -> 4096 <= (V 36%nat) <= 140737488355327 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 1 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 1 ->
  L5.u8_at RSEGS M (V 36%nat) (V 40%nat) -> 0 <= (V 40%nat) <= 255 -> ((V 36%nat) + 1 <= ((V 2%nat) - 256) \/ ((V 2%nat) - 256) + 256 <= (V 36%nat)) -> ((V 36%nat) + 1 <= (V 10%nat) \/ (V 10%nat) + 24 <= (V 36%nat)) ->
  4096 <= (V 37%nat) <= 140737488355328 -> aligned (V 37%nat) 16 -> 4096 <= ((V 37%nat) + 4) <= 140737488355328 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 4 <= 2147446784) ->
  (65536 + 6848512 <= (V 37%nat) \/ (V 37%nat) + 4 <= 65536) -> L5.writable RSEGS M (V 37%nat) 4 -> (((V 2%nat) - 256) + 256 <= (V 37%nat) \/ (V 37%nat) + 4 <= ((V 2%nat) - 256)) -> ((V 10%nat) + 24 <= (V 37%nat) \/ (V 37%nat) + 4 <= (V 10%nat)) ->
  ((V 36%nat) + 1 <= (V 37%nat) \/ (V 37%nat) + 4 <= (V 36%nat)) -> L5.u8_at RSEGS M ((((V 37%nat) + 2) / 8) + 2147450880) 4 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 152) <= bv_unsigned a < ((V 2%nat) - 152) + 32) -> ~ (((V 37%nat) + 2) <= bv_unsigned a < ((V 37%nat) + 2) + 1) -> ~ (((V 2%nat) - 208) <= bv_unsigned a < ((V 2%nat) - 208) + 48) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 152) <= i < ((V 2%nat) - 152) + 32) -> ~ (((V 37%nat) + 2) <= i < ((V 37%nat) + 2) + 1) -> ~ (((V 2%nat) - 208) <= i < ((V 2%nat) - 208) + 48) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xaf1e8 M) (st fx' R' 0xaa6ec M')
        /\ (forall x, In x KS_askS2t -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 717796
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 208)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 152)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 10%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1317368
        /\ getr R' (reg 12) = Z_to_bv 64 4
        /\ getr R' (reg 13) = Z_to_bv 64 2
        /\ getr R' (reg 19) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) ((V 37%nat) + 4)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) (V 10%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) ((V 10%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) 717380
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) ((V 37%nat) + 3)
        /\ L5.u8_at RSEGS M' ((V 37%nat) + 2) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 37%nat) + 4)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) ((V 37%nat) + 2)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 37%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G22 K0 K1 K2 pvzI8 K4 K5 K6 pvzI9 K8 K9 K10 K11 K12 pvzI10 K14 K15 K16 pvzI11 K18 K19 pvzI12 K21 pvzI13 K23 K24 K25 K26 K27 K28 K29.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV40l; move HV40l before pvzI5; pose proof (proj2 pvzI5) as HV40r; move HV40r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV56l; move HV56l before pvzI6; pose proof (proj2 pvzI6) as HV56r; move HV56r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV57l; move HV57l before pvzI7; pose proof (proj2 pvzI7) as HV57r; move HV57r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K7l; move K7l before pvzI9; pose proof (proj2 pvzI9) as K7r; move K7r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K13l; move K13l before pvzI10; pose proof (proj2 pvzI10) as K13r; move K13r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K17l; move K17l before pvzI11; pose proof (proj2 pvzI11) as K17r; move K17r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K20l; move K20l before pvzI12; pose proof (proj2 pvzI12) as K20r; move K20r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K22l; move K22l before pvzI13; pose proof (proj2 pvzI13) as K22r; move K22r before pvzI13; clear pvzI13.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 40%nat => Z_to_bv 64 vz_40 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 36%nat => vz_36 | 37%nat => vz_37 | 40%nat => vz_40 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PaskS2t.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaskS2t.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaskS2t.kn0).
  { unfold know_ok, PaskS2t.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28; lia | clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28; lia | byte_tac ltac:(clear) | exactA K29]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaskS2t.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaskS2t.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 152) <= bv_unsigned a < (vz_2 - 152) + 32) -> ~ ((vz_37 + 2) <= bv_unsigned a < (vz_37 + 2) + 1) -> ~ ((vz_2 - 208) <= bv_unsigned a < (vz_2 - 208) + 48) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PaskS2t.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18 K26 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk' ZA Hag ltac:(clear) | clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18 K26 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaskS2t.ps0) with 0xaa6ec in Hms. change (SR.ps_regs PaskS2t.ps0) with (map (fun i => (i, nth i PaskS2t.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaskS2t.ps0) with PaskS2t.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaskS2t.regs0 PaskS2t.regs_out0 60 KS_askS2t KS_askS2t_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaskS2t.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaskS2t.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS2t.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaskS2t.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS2t.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaskS2t.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS2t.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaskS2t.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS2t.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaskS2t.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS2t.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PaskS2t.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS2t.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PaskS2t.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS2t.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaskS2t.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K28) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K17l K17r) | byte_tac ltac:(clear - HV40l HV40r K17l K17r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | clear; lia].
Qed.

Module PaskS2 := BndP_Ea_049S8.LibSegEa_askS2.
Definition KS_askS2 : list nat := Eval vm_compute in (BG.kept_list 60 PaskS2.regs0 PaskS2.regs_out0).
Lemma KS_askS2_ok : BG.kept_ok 60 PaskS2.regs0 PaskS2.regs_out0 KS_askS2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma askS2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 9) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 37%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 (V 38%nat) -> getr R (reg 20) = Z_to_bv 64 ((((V 10%nat) + 8) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) ->
  L5.img_clear M 1253376 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 -> 6914048 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 10%nat) 24 ->
  (((V 2%nat) - 256) + 256 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 256)) -> 4096 <= (V 36%nat) <= 140737488355327 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 1 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 1 ->
  L5.u8_at RSEGS M (V 36%nat) (V 40%nat) -> 0 <= (V 40%nat) <= 255 -> ((V 36%nat) + 1 <= ((V 2%nat) - 256) \/ ((V 2%nat) - 256) + 256 <= (V 36%nat)) -> ((V 36%nat) + 1 <= (V 10%nat) \/ (V 10%nat) + 24 <= (V 36%nat)) ->
  4096 <= (V 37%nat) <= 140737488355328 -> aligned (V 37%nat) 16 -> 4096 <= ((V 37%nat) + (V 38%nat)) <= 140737488355328 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + (V 38%nat) <= 2147446784) ->
  (65536 + 6848512 <= (V 37%nat) \/ (V 37%nat) + (V 38%nat) <= 65536) -> L5.writable RSEGS M (V 37%nat) (V 38%nat) -> (((V 2%nat) - 256) + 256 <= (V 37%nat) \/ (V 37%nat) + (V 38%nat) <= ((V 2%nat) - 256)) -> ((V 10%nat) + 24 <= (V 37%nat) \/ (V 37%nat) + (V 38%nat) <= (V 10%nat)) ->
  ((V 36%nat) + 1 <= (V 37%nat) \/ (V 37%nat) + (V 38%nat) <= (V 36%nat)) -> 4 <= (V 34%nat) <= 8589934592 -> 8 <= (V 38%nat) <= 17179869184 -> 4 <= ((V 38%nat) - (V 34%nat)) <= 17179869184 ->
  L5KA.zeros_at M ((((V 34%nat) + (V 37%nat)) / 8) + 2147450880) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 152) <= bv_unsigned a < ((V 2%nat) - 152) + 32) -> ~ ((((V 34%nat) + (V 37%nat)) + 0) <= bv_unsigned a < (((V 34%nat) + (V 37%nat)) + 0) + 1) -> ~ (((V 2%nat) - 208) <= bv_unsigned a < ((V 2%nat) - 208) + 48) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 152) <= i < ((V 2%nat) - 152) + 32) -> ~ ((((V 34%nat) + (V 37%nat)) + 0) <= i < (((V 34%nat) + (V 37%nat)) + 0) + 1) -> ~ (((V 2%nat) - 208) <= i < ((V 2%nat) - 208) + 48) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xaf1e8 M) (st fx' R' 0xaa6ec M')
        /\ (forall x, In x KS_askS2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 717796
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 208)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 152)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 10%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1317368
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 19) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) ((V 37%nat) + (V 38%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) (V 10%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) ((V 10%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) 717380
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (((V 34%nat) + (V 37%nat)) + 1)
        /\ L5.u8_at RSEGS M' ((V 34%nat) + (V 37%nat)) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 37%nat) + (V 38%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) ((V 34%nat) + (V 37%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 37%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G22 K0 K1 K2 pvzI10 K4 K5 K6 pvzI11 K8 K9 K10 K11 K12 pvzI12 K14 K15 K16 pvzI13 K18 K19 pvzI14 K21 pvzI15 K23 K24 K25 K26 K27 K28 pvzI16 pvzI17 pvzI18 K32.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV40l; move HV40l before pvzI7; pose proof (proj2 pvzI7) as HV40r; move HV40r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV56l; move HV56l before pvzI8; pose proof (proj2 pvzI8) as HV56r; move HV56r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV57l; move HV57l before pvzI9; pose proof (proj2 pvzI9) as HV57r; move HV57r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K7l; move K7l before pvzI11; pose proof (proj2 pvzI11) as K7r; move K7r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K13l; move K13l before pvzI12; pose proof (proj2 pvzI12) as K13r; move K13r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K17l; move K17l before pvzI13; pose proof (proj2 pvzI13) as K17r; move K17r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K20l; move K20l before pvzI14; pose proof (proj2 pvzI14) as K20r; move K20r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K22l; move K22l before pvzI15; pose proof (proj2 pvzI15) as K22r; move K22r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K29l; move K29l before pvzI16; pose proof (proj2 pvzI16) as K29r; move K29r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K30l; move K30l before pvzI17; pose proof (proj2 pvzI17) as K30r; move K30r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K31l; move K31l before pvzI18; pose proof (proj2 pvzI18) as K31r; move K31r before pvzI18; clear pvzI18.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 40%nat => Z_to_bv 64 vz_40 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 34%nat => vz_34 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 40%nat => vz_40 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PaskS2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaskS2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaskS2.kn0).
  { unfold know_ok, PaskS2.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28 HV38l HV38r K30l K30r K31l K31r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk ZA ltac:(clear - HV38l HV38r K22l K22r K23 K24 K26 K27 K28 K30l K30r K31l K31r) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk ZA ltac:(clear - HV38l HV38r K22l K22r K23 K24 K26 K27 K28 K30l K30r K31l K31r) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk ZA ltac:(clear - HV38l HV38r K22l K22r K23 K24 K26 K27 K28 K30l K30r K31l K31r) | clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28 HV38l HV38r K30l K30r K31l K31r; lia | clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28 HV38l HV38r K30l K30r K31l K31r; lia | clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28 HV38l HV38r K30l K30r K31l K31r; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk ZA ltac:(clear - HV38l HV38r K22l K22r K23 K24 K26 K27 K28 K30l K30r K31l K31r) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk ZA ltac:(clear - HV38l HV38r K22l K22r K23 K24 K26 K27 K28 K30l K30r K31l K31r) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk ZA ltac:(clear - HV38l HV38r K22l K22r K23 K24 K26 K27 K28 K30l K30r K31l K31r) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K29l K29r K31l K31r) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K22l K22r K23 K24 K26 K27 K28 K30l K30r K31l K31r) | exact (conj K30l K30r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K29l K29r K31l K31r HV38l HV38r K22l K22r K23 K24 K26 K27 K28 K30l K30r) | exact (conj K31l K31r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K29l K29r K31l K31r HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K29l K29r K31l K31r HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28; lia | clear - HV34l HV34r K29l K29r K31l K31r HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28; lia | clear - HV34l HV34r K29l K29r K31l K31r HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28; lia | exactA K32]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaskS2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaskS2.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 152) <= bv_unsigned a < (vz_2 - 152) + 32) -> ~ (((vz_34 + vz_37) + 0) <= bv_unsigned a < ((vz_34 + vz_37) + 0) + 1) -> ~ ((vz_2 - 208) <= bv_unsigned a < (vz_2 - 208) + 48) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PaskS2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18 K26 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV34l HV34r K29l K29r K31l K31r HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk' ZA Hag ltac:(clear) | clear - HV34l HV34r K29l K29r K31l K31r HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K18 K26 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaskS2.ps0) with 0xaa6ec in Hms. change (SR.ps_regs PaskS2.ps0) with (map (fun i => (i, nth i PaskS2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaskS2.ps0) with PaskS2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaskS2.regs0 PaskS2.regs_out0 60 KS_askS2 KS_askS2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaskS2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaskS2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS2.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaskS2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS2.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaskS2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaskS2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaskS2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PaskS2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS2.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaskS2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28 HV38l HV38r K30l K30r K31l K31r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K13l K13r K14 K18 K19 K28) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV10l HV10r K7l K7r K9 K12 K19 K27) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K29l K29r K31l K31r HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV34l HV34r K29l K29r K31l K31r HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K17l K17r) | byte_tac ltac:(clear - HV40l HV40r K17l K17r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28 HV38l HV38r K30l K30r K31l K31r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K29l K29r K31l K31r HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12 K18 K26) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K20l K20r K22l K22r K23 K24 K26 K27 K28) | clear; lia].
Qed.

Module PaskW2 := BndP_Ea_050S8.LibSegEa_askW2.
Definition KS_askW2 : list nat := Eval vm_compute in (BG.kept_list 60 PaskW2.regs0 PaskW2.regs_out0).
Lemma KS_askW2_ok : BG.kept_ok 60 PaskW2.regs0 PaskW2.regs_out0 KS_askW2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma askW2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 208) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 152) -> getr R (reg 9) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 ((((V 10%nat) + 8) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1253376 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 -> 6914048 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 10%nat) 24 ->
  (((V 2%nat) - 256) + 256 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 256)) -> L5.u64_at RSEGS M (V 10%nat) (V 33%nat) -> L5.u64_at RSEGS M ((V 10%nat) + 8) ((V 33%nat) + (V 34%nat)) -> L5.u64_at RSEGS M ((V 10%nat) + 16) ((V 33%nat) + (V 35%nat)) ->
  0 <= (V 33%nat) <= 140737488355328 -> 0 <= (V 34%nat) <= 17179869184 -> 0 <= (V 35%nat) <= 17179869184 -> 0 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 ->
  L5.u64_at RSEGS M ((V 2%nat) - 152) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((V 34%nat) + (V 37%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 136) (((V 34%nat) + (V 37%nat)) + 1) -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 37%nat) + (V 38%nat)) ->
  4096 <= (V 37%nat) <= 140737488355328 -> 4096 <= ((V 34%nat) + (V 37%nat)) <= 140737488355327 -> 4096 <= ((V 37%nat) + (V 38%nat)) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xaf3e4 M) (st fx' R' 0x78618 M')
        /\ (forall x, In x KS_askW2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 717884
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 37%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 K0 K1 K2 pvzI12 K4 K5 K6 pvzI13 K8 K9 K10 K11 K12 K13 K14 K15 pvzI14 pvzI15 pvzI16 pvzI17 K20 K21 K22 K23 pvzI18 pvzI19 pvzI20.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV35l; move HV35l before pvzI5; pose proof (proj2 pvzI5) as HV35r; move HV35r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV36l; move HV36l before pvzI6; pose proof (proj2 pvzI6) as HV36r; move HV36r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV37l; move HV37l before pvzI7; pose proof (proj2 pvzI7) as HV37r; move HV37r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV38l; move HV38l before pvzI8; pose proof (proj2 pvzI8) as HV38r; move HV38r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV55l; move HV55l before pvzI9; pose proof (proj2 pvzI9) as HV55r; move HV55r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV56l; move HV56l before pvzI10; pose proof (proj2 pvzI10) as HV56r; move HV56r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV57l; move HV57l before pvzI11; pose proof (proj2 pvzI11) as HV57r; move HV57r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K3l; move K3l before pvzI12; pose proof (proj2 pvzI12) as K3r; move K3r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K7l; move K7l before pvzI13; pose proof (proj2 pvzI13) as K7r; move K7r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K16l; move K16l before pvzI14; pose proof (proj2 pvzI14) as K16r; move K16r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K17l; move K17l before pvzI15; pose proof (proj2 pvzI15) as K17r; move K17r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K18l; move K18l before pvzI16; pose proof (proj2 pvzI16) as K18r; move K18r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K19l; move K19l before pvzI17; pose proof (proj2 pvzI17) as K19r; move K19r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K24l; move K24l before pvzI18; pose proof (proj2 pvzI18) as K24r; move K24r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K25l; move K25l before pvzI19; pose proof (proj2 pvzI19) as K25r; move K25r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K26l; move K26l before pvzI20; pose proof (proj2 pvzI20) as K26r; move K26r before pvzI20; clear pvzI20.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PaskW2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaskW2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaskW2.kn0).
  { unfold know_ok, PaskW2.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV37l HV37r K24l K24r K25l K25r K26l K26r HV38l HV38r) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K24l K24r K25l K25r K26l K26r) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K17l K17r K25l K25r HV37l HV37r K24l K24r K26l K26r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K24l K24r K25l K25r K26l K26r HV38l HV38r) | exact (conj K26l K26r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaskW2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaskW2.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PaskW2.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaskW2.ps0) with 0x78618 in Hms. change (SR.ps_regs PaskW2.ps0) with (map (fun i => (i, nth i PaskW2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaskW2.ps0) with PaskW2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaskW2.regs0 PaskW2.regs_out0 60 KS_askW2 KS_askW2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaskW2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaskW2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskW2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaskW2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskW2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaskW2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskW2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PaskW2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PaskW2.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaskW2.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PaskW3 := BndP_Ea_050S8.LibSegEa_askW3.
Definition KS_askW3 : list nat := Eval vm_compute in (BG.kept_list 60 PaskW3.regs0 PaskW3.regs_out0).
Lemma KS_askW3_ok : BG.kept_ok 60 PaskW3.regs0 PaskW3.regs_out0 KS_askW3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma askW3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 208) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 152) -> getr R (reg 9) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 ((((V 10%nat) + 8) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1253376 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 -> 6914048 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 10%nat) 24 ->
  (((V 2%nat) - 256) + 256 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 256)) -> L5.u64_at RSEGS M (V 10%nat) (V 33%nat) -> L5.u64_at RSEGS M ((V 10%nat) + 8) ((V 33%nat) + (V 34%nat)) -> L5.u64_at RSEGS M ((V 10%nat) + 16) ((V 33%nat) + (V 35%nat)) ->
  0 <= (V 33%nat) <= 140737488355328 -> 0 <= (V 34%nat) <= 17179869184 -> 0 <= (V 35%nat) <= 17179869184 -> 0 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 ->
  L5.u64_at RSEGS M ((V 2%nat) - 152) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((V 34%nat) + (V 37%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 136) (((V 34%nat) + (V 37%nat)) + 1) -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 37%nat) + (V 38%nat)) ->
  4096 <= (V 37%nat) <= 140737488355328 -> 4096 <= ((V 34%nat) + (V 37%nat)) <= 140737488355327 -> 4096 <= ((V 37%nat) + (V 38%nat)) <= 140737488355328 -> L5.u64_at RSEGS M ((V 2%nat) - 168) 717380 ->
  L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 10%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 184) (V 10%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 36%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 200) ((V 37%nat) + (V 38%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 152) <= bv_unsigned a < ((V 2%nat) - 152) + 32) -> ~ (((V 10%nat) + 0) <= bv_unsigned a < ((V 10%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 152) <= i < ((V 2%nat) - 152) + 32) -> ~ (((V 10%nat) + 0) <= i < ((V 10%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xaf43c M) (st fx' R' 0xaf538 M')
        /\ (forall x, In x KS_askW3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 717380
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 160)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 10%nat) + 8)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 10%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 34%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 37%nat) + (V 38%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + (V 35%nat))
        /\ L5.u64_at RSEGS M' ((V 10%nat) + 16) ((V 37%nat) + (V 38%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 10%nat) + 8) (((V 34%nat) + (V 37%nat)) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 33%nat)
        /\ L5.u64_at RSEGS M' (V 10%nat) (V 37%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 K0 K1 K2 pvzI12 K4 K5 K6 pvzI13 K8 K9 K10 K11 K12 K13 K14 K15 pvzI14 pvzI15 pvzI16 pvzI17 K20 K21 K22 K23 pvzI18 pvzI19 pvzI20 K27 K28 K29 K30 K31.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV35l; move HV35l before pvzI5; pose proof (proj2 pvzI5) as HV35r; move HV35r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV36l; move HV36l before pvzI6; pose proof (proj2 pvzI6) as HV36r; move HV36r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV37l; move HV37l before pvzI7; pose proof (proj2 pvzI7) as HV37r; move HV37r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV38l; move HV38l before pvzI8; pose proof (proj2 pvzI8) as HV38r; move HV38r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV55l; move HV55l before pvzI9; pose proof (proj2 pvzI9) as HV55r; move HV55r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV56l; move HV56l before pvzI10; pose proof (proj2 pvzI10) as HV56r; move HV56r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV57l; move HV57l before pvzI11; pose proof (proj2 pvzI11) as HV57r; move HV57r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K3l; move K3l before pvzI12; pose proof (proj2 pvzI12) as K3r; move K3r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K7l; move K7l before pvzI13; pose proof (proj2 pvzI13) as K7r; move K7r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K16l; move K16l before pvzI14; pose proof (proj2 pvzI14) as K16r; move K16r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K17l; move K17l before pvzI15; pose proof (proj2 pvzI15) as K17r; move K17r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K18l; move K18l before pvzI16; pose proof (proj2 pvzI16) as K18r; move K18r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K19l; move K19l before pvzI17; pose proof (proj2 pvzI17) as K19r; move K19r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K24l; move K24l before pvzI18; pose proof (proj2 pvzI18) as K24r; move K24r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K25l; move K25l before pvzI19; pose proof (proj2 pvzI19) as K25r; move K25r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K26l; move K26l before pvzI20; pose proof (proj2 pvzI20) as K26r; move K26r before pvzI20; clear pvzI20.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PaskW3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaskW3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaskW3.kn0).
  { unfold know_ok, PaskW3.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV37l HV37r K24l K24r K25l K25r K26l K26r HV38l HV38r) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K24l K24r K25l K25r K26l K26r) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K17l K17r K25l K25r HV37l HV37r K24l K24r K26l K26r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K24l K24r K25l K25r K26l K26r HV38l HV38r) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV37l HV37r K24l K24r K25l K25r K26l K26r HV38l HV38r) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K31]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaskW3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaskW3.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 152) <= bv_unsigned a < (vz_2 - 152) + 32) -> ~ ((vz_10 + 0) <= bv_unsigned a < (vz_10 + 0) + 24) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PaskW3.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K12 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV10l HV10r K7l K7r K9 K12) | evalEk' ZA Hag ltac:(clear) | clear - HV10l HV10r K7l K7r K9 K12 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaskW3.ps0) with 0xaf538 in Hms. change (SR.ps_regs PaskW3.ps0) with (map (fun i => (i, nth i PaskW3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaskW3.ps0) with PaskW3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaskW3.regs0 PaskW3.regs_out0 60 KS_askW3 KS_askW3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaskW3.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaskW3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskW3.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaskW3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskW3.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaskW3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskW3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaskW3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskW3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaskW3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskW3.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PaskW3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskW3.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaskW3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskW3.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaskW3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K16l K16r K19l K19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K16l K16r K19l K19r HV35l HV35r K18l K18r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K7l K7r K9 K12) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K24l K24r K25l K25r K26l K26r HV38l HV38r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K16l K16r K19l K19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K7l K7r K9 K12) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K17l K17r K25l K25r HV37l HV37r K24l K24r K26l K26r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K16l K16r K19l K19r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K7l K7r K9 K12) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K24l K24r K25l K25r K26l K26r) | clear; lia].
Qed.

Module PaskS3n := BndP_Ea_049S8.LibSegEa_askS3n.
Definition KS_askS3n : list nat := Eval vm_compute in (BG.kept_list 60 PaskS3n.regs0 PaskS3n.regs_out0).
Lemma KS_askS3n_ok : BG.kept_ok 60 PaskS3n.regs0 PaskS3n.regs_out0 KS_askS3n = true. Proof. vm_compute. reflexivity. Qed.
Lemma askS3n_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 9) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 ((((V 10%nat) + 8) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 0 ->
  L5.img_clear M 1253376 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 -> 6914048 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 10%nat) 24 ->
  (((V 2%nat) - 256) + 256 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 256)) -> L5.u64_at RSEGS M ((V 10%nat) + 8) ((V 37%nat) + 1) -> L5.u64_at RSEGS M ((V 2%nat) - 152) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 144) 0 ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 128) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 56) 717004 -> L5.u64_at RSEGS M ((V 2%nat) - 64) ((V 10%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 72) (V 36%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 88) ((((V 10%nat) + 8) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 96) 2147450880 ->
  L5.u64_at RSEGS M ((V 2%nat) - 104) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 112) (V 51%nat) -> 4096 <= (V 37%nat) <= 140737488355327 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 136) <= bv_unsigned a < ((V 2%nat) - 136) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 136) <= i < ((V 2%nat) - 136) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xaf244 M) (st fx' R' 0xaf29c M')
        /\ (forall x, In x KS_askS3n -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 717004
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 37%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 0
        /\ getr R' (reg 19) = Z_to_bv 64 ((((V 10%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 20) = Z_to_bv 64 2147450880
        /\ getr R' (reg 21) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 51%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G8 G9 G10 G11 G12 G18 G20 G21 G22 K0 K1 K2 pvzI10 K4 K5 K6 pvzI11 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 pvzI12.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV55l; move HV55l before pvzI7; pose proof (proj2 pvzI7) as HV55r; move HV55r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV56l; move HV56l before pvzI8; pose proof (proj2 pvzI8) as HV56r; move HV56r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV57l; move HV57l before pvzI9; pose proof (proj2 pvzI9) as HV57r; move HV57r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K7l; move K7l before pvzI11; pose proof (proj2 pvzI11) as K7r; move K7r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K26l; move K26l before pvzI12; pose proof (proj2 pvzI12) as K26r; move K26r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 36%nat => vz_36 | 37%nat => vz_37 | 50%nat => vz_50 | 51%nat => vz_51 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PaskS3n.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaskS3n.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaskS3n.kn0).
  { unfold know_ok, PaskS3n.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | evalEk ZA ltac:(clear - HV37l HV37r K26l K26r) | clear - HV10l HV10r K7l K7r K9 K12; lia | clear - HV10l HV10r K7l K7r K9 K12; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K26l K26r) | exact (conj K26l K26r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaskS3n.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaskS3n.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 136) <= bv_unsigned a < (vz_2 - 136) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PaskS3n.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K12 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaskS3n.ps0) with 0xaf29c in Hms. change (SR.ps_regs PaskS3n.ps0) with (map (fun i => (i, nth i PaskS3n.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaskS3n.ps0) with PaskS3n.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaskS3n.regs0 PaskS3n.regs_out0 60 KS_askS3n KS_askS3n_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaskS3n.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaskS3n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS3n.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaskS3n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS3n.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PaskS3n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS3n.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaskS3n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS3n.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaskS3n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS3n.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaskS3n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS3n.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaskS3n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS3n.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PaskS3n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS3n.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PaskS3n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PaskS3n.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PaskS3n.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PaskS3 := BndP_Ea_049S8.LibSegEa_askS3.
Definition KS_askS3 : list nat := Eval vm_compute in (BG.kept_list 60 PaskS3.regs0 PaskS3.regs_out0).
Lemma KS_askS3_ok : BG.kept_ok 60 PaskS3.regs0 PaskS3.regs_out0 KS_askS3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma askS3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 9) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 ((((V 10%nat) + 8) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) ->
  L5.img_clear M 1253376 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 -> 6914048 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 10%nat) 24 ->
  (((V 2%nat) - 256) + 256 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 256)) -> L5.u64_at RSEGS M ((V 10%nat) + 8) (((V 34%nat) + (V 37%nat)) + 1) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + (V 35%nat)) -> 4096 <= (V 33%nat) <= 140737488355328 -> aligned (V 33%nat) 16 ->
  0 <= (V 34%nat) <= 17179869184 -> 0 <= (V 35%nat) <= 17179869184 -> 4096 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + (V 35%nat) <= 2147446784) ->
  (65536 + 6848512 <= (V 33%nat) \/ (V 33%nat) + (V 35%nat) <= 65536) -> 4096 <= (V 37%nat) <= 140737488355328 -> 4096 <= ((V 34%nat) + (V 37%nat)) <= 140737488355327 -> 4096 <= ((V 37%nat) + (V 38%nat)) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 136) <= bv_unsigned a < ((V 2%nat) - 136) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 136) <= i < ((V 2%nat) - 136) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xaf244 M) (st fx' R' 0xd4a60 M')
        /\ (forall x, In x KS_askS3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 717428
        /\ getr R' (reg 8) = Z_to_bv 64 (((V 34%nat) + (V 37%nat)) + 1)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 33%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 G2 G8 G9 G10 G11 G12 G18 G20 G21 G22 K0 K1 K2 pvzI12 K4 K5 K6 pvzI13 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 pvzI14 K19 pvzI15 pvzI16 pvzI17 K23 K24 pvzI18 pvzI19 pvzI20.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV35l; move HV35l before pvzI5; pose proof (proj2 pvzI5) as HV35r; move HV35r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV36l; move HV36l before pvzI6; pose proof (proj2 pvzI6) as HV36r; move HV36r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV37l; move HV37l before pvzI7; pose proof (proj2 pvzI7) as HV37r; move HV37r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV38l; move HV38l before pvzI8; pose proof (proj2 pvzI8) as HV38r; move HV38r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV55l; move HV55l before pvzI9; pose proof (proj2 pvzI9) as HV55r; move HV55r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV56l; move HV56l before pvzI10; pose proof (proj2 pvzI10) as HV56r; move HV56r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV57l; move HV57l before pvzI11; pose proof (proj2 pvzI11) as HV57r; move HV57r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K3l; move K3l before pvzI12; pose proof (proj2 pvzI12) as K3r; move K3r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K7l; move K7l before pvzI13; pose proof (proj2 pvzI13) as K7r; move K7r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K18l; move K18l before pvzI14; pose proof (proj2 pvzI14) as K18r; move K18r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K20l; move K20l before pvzI15; pose proof (proj2 pvzI15) as K20r; move K20r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K21l; move K21l before pvzI16; pose proof (proj2 pvzI16) as K21r; move K21r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K22l; move K22l before pvzI17; pose proof (proj2 pvzI17) as K22r; move K22r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K25l; move K25l before pvzI18; pose proof (proj2 pvzI18) as K25r; move K25r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K26l; move K26l before pvzI19; pose proof (proj2 pvzI19) as K26r; move K26r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K27l; move K27l before pvzI20; pose proof (proj2 pvzI20) as K27r; move K27r before pvzI20; clear pvzI20.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PaskS3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaskS3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaskS3.kn0).
  { unfold know_ok, PaskS3.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K25l K25r K26l K26r K27l K27r HV38l HV38r) | exact (conj K27l K27r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaskS3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaskS3.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 136) <= bv_unsigned a < (vz_2 - 136) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PaskS3.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K12 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaskS3.ps0) with 0xd4a60 in Hms. change (SR.ps_regs PaskS3.ps0) with (map (fun i => (i, nth i PaskS3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaskS3.ps0) with PaskS3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaskS3.regs0 PaskS3.regs_out0 60 KS_askS3 KS_askS3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaskS3.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaskS3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS3.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaskS3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaskS3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaskS3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K18l K18r K22l K22r K23 K24) | clear; lia].
Qed.

Module PaskS4 := BndP_Ea_049S8.LibSegEa_askS4.
Definition KS_askS4 : list nat := Eval vm_compute in (BG.kept_list 60 PaskS4.regs0 PaskS4.regs_out0).
Lemma KS_askS4_ok : BG.kept_ok 60 PaskS4.regs0 PaskS4.regs_out0 KS_askS4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma askS4_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 41%nat) -> getr R (reg 9) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 ((((V 10%nat) + 8) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1253376 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 -> 6914048 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 10%nat) 24 ->
  (((V 2%nat) - 256) + 256 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 256)) -> L5.u64_at RSEGS M ((V 2%nat) - 56) 717004 -> L5.u64_at RSEGS M ((V 2%nat) - 64) ((V 10%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 36%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) ((V 33%nat) + (V 34%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 88) ((((V 10%nat) + 8) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 96) 2147450880 -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 112) (V 51%nat) -> 0 <= (V 33%nat) <= 140737488355328 -> 0 <= (V 34%nat) <= 17179869184 -> 0 <= (V 35%nat) <= 17179869184 ->
  0 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xaf274 M) (st fx' R' 0xaf29c M')
        /\ (forall x, In x KS_askS4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 717004
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 10%nat) + 8)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 33%nat) + (V 34%nat))
        /\ getr R' (reg 19) = Z_to_bv 64 ((((V 10%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 20) = Z_to_bv 64 2147450880
        /\ getr R' (reg 21) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 51%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 G2 G8 G9 G10 G11 G12 G18 G20 G21 K0 K1 K2 pvzI13 K4 K5 K6 pvzI14 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 pvzI15 pvzI16 pvzI17 pvzI18.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV35l; move HV35l before pvzI5; pose proof (proj2 pvzI5) as HV35r; move HV35r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV36l; move HV36l before pvzI6; pose proof (proj2 pvzI6) as HV36r; move HV36r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV41l; move HV41l before pvzI7; pose proof (proj2 pvzI7) as HV41r; move HV41r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV50l; move HV50l before pvzI8; pose proof (proj2 pvzI8) as HV50r; move HV50r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV51l; move HV51l before pvzI9; pose proof (proj2 pvzI9) as HV51r; move HV51r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV55l; move HV55l before pvzI10; pose proof (proj2 pvzI10) as HV55r; move HV55r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV56l; move HV56l before pvzI11; pose proof (proj2 pvzI11) as HV56r; move HV56r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV57l; move HV57l before pvzI12; pose proof (proj2 pvzI12) as HV57r; move HV57r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K3l; move K3l before pvzI13; pose proof (proj2 pvzI13) as K3r; move K3r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K7l; move K7l before pvzI14; pose proof (proj2 pvzI14) as K7r; move K7r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K21l; move K21l before pvzI15; pose proof (proj2 pvzI15) as K21r; move K21r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K22l; move K22l before pvzI16; pose proof (proj2 pvzI16) as K22r; move K22r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K23l; move K23l before pvzI17; pose proof (proj2 pvzI17) as K23r; move K23r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K24l; move K24l before pvzI18; pose proof (proj2 pvzI18) as K24r; move K24r before pvzI18; clear pvzI18.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 41%nat => Z_to_bv 64 vz_41 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 41%nat => vz_41 | 50%nat => vz_50 | 51%nat => vz_51 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PaskS4.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaskS4.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaskS4.kn0).
  { unfold know_ok, PaskS4.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV33l HV33r K21l K21r K24l K24r HV34l HV34r K22l K22r) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV10l HV10r K7l K7r K9 K12) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K3l K3r K12; lia | clear - HV2l HV2r K3l K3r K12; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K21l K21r K24l K24r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K23l K23r K24l K24r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K21l K21r K24l K24r HV35l HV35r K23l K23r) | exact (conj K24l K24r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaskS4.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaskS4.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PaskS4.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaskS4.ps0) with 0xaf29c in Hms. change (SR.ps_regs PaskS4.ps0) with (map (fun i => (i, nth i PaskS4.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaskS4.ps0) with PaskS4.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaskS4.regs0 PaskS4.regs_out0 60 KS_askS4 KS_askS4_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaskS4.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaskS4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS4.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaskS4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS4.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaskS4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS4.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PaskS4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS4.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaskS4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS4.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaskS4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS4.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaskS4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS4.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PaskS4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaskS4.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PaskS4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PaskS4.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PaskS4.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

End PEASKPP.
