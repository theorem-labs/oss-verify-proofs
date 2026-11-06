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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.seg Require BndP_Ea_001S8 BndP_Ea_002S8 BndP_Ea_003S8.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEABAP1.
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

Module PabaA := BndP_Ea_001S8.LibSegEa_abaA.
Definition KS_abaA : list nat := Eval vm_compute in (BG.kept_list 72 PabaA.regs0 PabaA.regs_out0).
Lemma KS_abaA_ok : BG.kept_ok 72 PabaA.regs0 PabaA.regs_out0 KS_abaA = true. Proof. vm_compute. reflexivity. Qed.
Lemma abaA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 (V 37%nat) -> getr R (reg 12) = Z_to_bv 64 (V 38%nat) ->
  L5.img_clear M 65536 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6914048 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 160) + 160 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 160)) -> 6914048 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 160) + 160 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 160)) ->
  6914048 <= (V 37%nat) <= 140737488355320 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 37%nat) 8 -> (((V 2%nat) - 160) + 160 <= (V 37%nat) \/ (V 37%nat) + 8 <= ((V 2%nat) - 160)) -> ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 36%nat)) ->
  ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 38%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb693c M) (st fx' R' 0x5e414 M')
        /\ (forall x, In x KS_abaA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 747956
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 10) = Z_to_bv 64 64
        /\ getr R' (reg 11) = Z_to_bv 64 1317368
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 19) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 37%nat)
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
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G10 G11 G12 K0 K1 K2 pvzI5 K4 K5 pvzI6 K7 K8 K9 K10 K11 K12 K13 pvzI7 K15 K16 K17 K18 K19 pvzI8 K21 K22 K23 K24 K25 K26 K27 K28.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K3l; move K3l before pvzI5; pose proof (proj2 pvzI5) as K3r; move K3r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K6l; move K6l before pvzI6; pose proof (proj2 pvzI6) as K6r; move K6r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K14l; move K14l before pvzI7; pose proof (proj2 pvzI7) as K14r; move K14r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K20l; move K20l before pvzI8; pose proof (proj2 pvzI8) as K20r; move K20r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 39%nat. }
  assert (HR: regs_ok E PabaA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PabaA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PabaA.kn0).
  { unfold know_ok, PabaA.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | clear; lia | exact K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PabaA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PabaA.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 128) <= bv_unsigned a < (vz_2 - 128) + 128) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PabaA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PabaA.ps0) with 0x5e414 in Hms. change (SR.ps_regs PabaA.ps0) with (map (fun i => (i, nth i PabaA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PabaA.ps0) with PabaA.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PabaA.regs0 PabaA.regs_out0 72 KS_abaA KS_abaA_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PabaA.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PabaA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaA.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PabaA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaA.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PabaA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaA.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PabaA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaA.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PabaA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaA.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PabaA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaA.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PabaA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaA.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PabaA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaA.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PabaA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaA.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PabaA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaA.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PabaA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
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

Module PabaB0 := BndP_Ea_001S8.LibSegEa_abaB0.
Definition KS_abaB0 : list nat := Eval vm_compute in (BG.kept_list 72 PabaB0.regs0 PabaB0.regs_out0).
Lemma KS_abaB0_ok : BG.kept_ok 72 PabaB0.regs0 PabaB0.regs_out0 KS_abaB0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma abaB0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 (V 37%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6914048 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 160) + 160 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 160)) -> 6914048 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 160) + 160 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 160)) ->
  6914048 <= (V 37%nat) <= 140737488355320 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 37%nat) 8 -> (((V 2%nat) - 160) + 160 <= (V 37%nat) \/ (V 37%nat) + 8 <= ((V 2%nat) - 160)) -> ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 36%nat)) ->
  ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 38%nat)) -> 6914048 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 64 ->
  L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 -> L5KA.zeros_at M (((V 47%nat) / 8) + 2147450880) 8 ->
  L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) ->
  ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 160) + 160 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 36%nat)) ->
  ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) -> ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 36%nat) / 8) + 2147450880)) -> ((V 38%nat) + 16 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 38%nat)) -> ((V 38%nat) + 16 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 38%nat)) ->
  ((((V 38%nat) / 8) + 2147450880) + 2 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 38%nat) / 8) + 2147450880)) -> ((V 37%nat) + 8 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 37%nat)) -> ((V 37%nat) + 8 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 37%nat)) -> ((((V 37%nat) / 8) + 2147450880) + 1 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 37%nat) / 8) + 2147450880)) ->
  ((V 47%nat) + 64 <= 65536 \/ 65536 + 1196128 <= (V 47%nat)) -> L5.u32_at RSEGS M ((V 36%nat) + 12) (V 33%nat) -> L5.u32_at RSEGS M ((V 36%nat) + 320) 1024 -> 0 <= (V 33%nat) <= 1023 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 8) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 36%nat) + 12) <= bv_unsigned a < ((V 36%nat) + 12) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 8) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 36%nat) + 12) <= i < ((V 36%nat) + 12) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb69b4 M) (st fx' R' 0xb4bd0 M')
        /\ (forall x, In x KS_abaB0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 748168
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 24)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 18446744073709551603
        /\ getr R' (reg 14) = Z_to_bv 64 18446744073709551608
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 36%nat) + 24)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880)
        /\ L5.u32_at RSEGS M' ((V 36%nat) + 12) ((V 33%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) (V 47%nat)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450883) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450882) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450881) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450880) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450887) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450885) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 248
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 16) 747836
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 8) 94784
        /\ L5.u64_at RSEGS M' (V 47%nat) 1102416563
        /\ L5.defined M' ((V 47%nat) + 24) 40).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G19 G20 G21 G27 K0 K1 K2 pvzI8 K4 K5 pvzI9 K7 K8 K9 K10 K11 K12 K13 pvzI10 K15 K16 K17 K18 K19 pvzI11 K21 K22 K23 K24 K25 K26 K27 K28 pvzI12 K30 K31 K32 K33 K34 K35 K36 pvzI13 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 pvzI14.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV47l; move HV47l before pvzI6; pose proof (proj2 pvzI6) as HV47r; move HV47r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV48l; move HV48l before pvzI7; pose proof (proj2 pvzI7) as HV48r; move HV48r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K14l; move K14l before pvzI10; pose proof (proj2 pvzI10) as K14r; move K14r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K20l; move K20l before pvzI11; pose proof (proj2 pvzI11) as K20r; move K20r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K29l; move K29l before pvzI12; pose proof (proj2 pvzI12) as K29r; move K29r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K37l; move K37l before pvzI13; pose proof (proj2 pvzI13) as K37r; move K37r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K55l; move K55l before pvzI14; pose proof (proj2 pvzI14) as K55r; move K55r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PabaB0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PabaB0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PabaB0.kn0).
  { unfold know_ok, PabaB0.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | clear; lia | exact K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | clear; lia | exact K30]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K34]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear - HV48l HV48r K37l K37r) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K37l K37r) | exact (conj K37l K37r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K37l K37r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K37l K37r; lia | clear - HV48l HV48r K37l K37r; lia | clear - HV48l HV48r K37l K37r; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K37l K37r) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K37l K37r) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K41; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K37l K37r) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K43; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K37l K37r) | evalEk ZA ltac:(clear) | generalize K44; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K45; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K37l K37r) | evalEk ZA ltac:(clear) | generalize K47; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K37l K37r) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K52; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear - HV33l HV33r K55l K55r) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K53]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K55l K55r) | exact (conj K55l K55r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PabaB0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PabaB0.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 128) <= bv_unsigned a < (vz_2 - 128) + 8) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 24) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 8) -> ~ ((vz_36 + 12) <= bv_unsigned a < (vz_36 + 12) + 4) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PabaB0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K29l K29r Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K29l K29r Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K6l K6r Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PabaB0.ps0) with 0xb4bd0 in Hms. change (SR.ps_regs PabaB0.ps0) with (map (fun i => (i, nth i PabaB0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PabaB0.ps0) with PabaB0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PabaB0.regs0 PabaB0.regs_out0 72 KS_abaB0 KS_abaB0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PabaB0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PabaB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaB0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PabaB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaB0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PabaB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaB0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PabaB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaB0.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PabaB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaB0.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PabaB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaB0.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PabaB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaB0.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PabaB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaB0.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PabaB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaB0.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PabaB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K55l K55r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PabaB1 := BndP_Ea_002S8.LibSegEa_abaB1.
Definition KS_abaB1 : list nat := Eval vm_compute in (BG.kept_list 72 PabaB1.regs0 PabaB1.regs_out0).
Lemma KS_abaB1_ok : BG.kept_ok 72 PabaB1.regs0 PabaB1.regs_out0 KS_abaB1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma abaB1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 (V 37%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6914048 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 160) + 160 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 160)) -> 6914048 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 160) + 160 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 160)) ->
  6914048 <= (V 37%nat) <= 140737488355320 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 37%nat) 8 -> (((V 2%nat) - 160) + 160 <= (V 37%nat) \/ (V 37%nat) + 8 <= ((V 2%nat) - 160)) -> ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 36%nat)) ->
  ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 38%nat)) -> 6914048 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 64 ->
  L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 -> L5KA.zeros_at M (((V 47%nat) / 8) + 2147450880) 8 ->
  L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) ->
  ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 160) + 160 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 36%nat)) ->
  ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) -> ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 36%nat) / 8) + 2147450880)) -> ((V 38%nat) + 16 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 38%nat)) -> ((V 38%nat) + 16 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 38%nat)) ->
  ((((V 38%nat) / 8) + 2147450880) + 2 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 38%nat) / 8) + 2147450880)) -> ((V 37%nat) + 8 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 37%nat)) -> ((V 37%nat) + 8 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 37%nat)) -> ((((V 37%nat) / 8) + 2147450880) + 1 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 37%nat) / 8) + 2147450880)) ->
  ((V 47%nat) + 64 <= 65536 \/ 65536 + 1196128 <= (V 47%nat)) -> L5.u32_at RSEGS M ((V 36%nat) + 12) 1024 -> L5.u32_at RSEGS M ((V 36%nat) + 320) 1024 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 8) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 36%nat) + 12) <= bv_unsigned a < ((V 36%nat) + 12) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 8) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 36%nat) + 12) <= i < ((V 36%nat) + 12) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb69b4 M) (st fx' R' 0xae310 M')
        /\ (forall x, In x KS_abaB1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 749184
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 11
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 18446744073709551603
        /\ getr R' (reg 14) = Z_to_bv 64 18446744073709551608
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880)
        /\ L5.u32_at RSEGS M' ((V 36%nat) + 12) 1025
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) (V 47%nat)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450883) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450882) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450881) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450880) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450887) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450885) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 248
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 16) 747836
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 8) 94784
        /\ L5.u64_at RSEGS M' (V 47%nat) 1102416563
        /\ L5.defined M' ((V 47%nat) + 24) 40).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G10 G19 G20 G21 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 pvzI9 K15 K16 K17 K18 K19 pvzI10 K21 K22 K23 K24 K25 K26 K27 K28 pvzI11 K30 K31 K32 K33 K34 K35 K36 pvzI12 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K20l; move K20l before pvzI10; pose proof (proj2 pvzI10) as K20r; move K20r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K29l; move K29l before pvzI11; pose proof (proj2 pvzI11) as K29r; move K29r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K37l; move K37l before pvzI12; pose proof (proj2 pvzI12) as K37r; move K37r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PabaB1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PabaB1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PabaB1.kn0).
  { unfold know_ok, PabaB1.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | clear; lia | exact K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | clear; lia | exact K30]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K34]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear - HV48l HV48r K37l K37r) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K37l K37r) | exact (conj K37l K37r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K37l K37r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K37l K37r; lia | clear - HV48l HV48r K37l K37r; lia | clear - HV48l HV48r K37l K37r; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K37l K37r) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K37l K37r) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K41; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K37l K37r) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K43; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K37l K37r) | evalEk ZA ltac:(clear) | generalize K44; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K45; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K37l K37r) | evalEk ZA ltac:(clear) | generalize K47; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K37l K37r) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K52; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K53]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K54]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PabaB1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PabaB1.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 128) <= bv_unsigned a < (vz_2 - 128) + 8) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 24) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 8) -> ~ ((vz_36 + 12) <= bv_unsigned a < (vz_36 + 12) + 4) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PabaB1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K29l K29r Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K29l K29r Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K6l K6r Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PabaB1.ps0) with 0xae310 in Hms. change (SR.ps_regs PabaB1.ps0) with (map (fun i => (i, nth i PabaB1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PabaB1.ps0) with PabaB1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PabaB1.regs0 PabaB1.regs_out0 72 KS_abaB1 KS_abaB1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PabaB1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PabaB1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaB1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PabaB1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaB1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PabaB1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaB1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PabaB1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaB1.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PabaB1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaB1.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PabaB1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaB1.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PabaB1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaB1.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PabaB1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaB1.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PabaB1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PabaKd := BndP_Ea_002S8.LibSegEa_abaKd.
Definition KS_abaKd : list nat := Eval vm_compute in (BG.kept_list 72 PabaKd.regs0 PabaKd.regs_out0).
Lemma KS_abaKd_ok : BG.kept_ok 72 PabaKd.regs0 PabaKd.regs_out0 KS_abaKd = true. Proof. vm_compute. reflexivity. Qed.
Lemma abaKd_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 36 -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 (V 37%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6914048 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 160) + 160 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 160)) -> 6914048 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 160) + 160 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 160)) ->
  6914048 <= (V 37%nat) <= 140737488355320 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 37%nat) 8 -> (((V 2%nat) - 160) + 160 <= (V 37%nat) \/ (V 37%nat) + 8 <= ((V 2%nat) - 160)) -> ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 36%nat)) ->
  ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 38%nat)) -> 6914048 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 64 ->
  L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) ->
  4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) ->
  (((V 2%nat) - 160) + 160 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) ->
  ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 36%nat) / 8) + 2147450880)) -> ((V 38%nat) + 16 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 38%nat)) -> ((V 38%nat) + 16 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 38%nat)) -> ((((V 38%nat) / 8) + 2147450880) + 2 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 38%nat) / 8) + 2147450880)) ->
  ((V 37%nat) + 8 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 37%nat)) -> ((V 37%nat) + 8 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 37%nat)) -> ((((V 37%nat) / 8) + 2147450880) + 1 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 37%nat) / 8) + 2147450880)) -> ((V 47%nat) + 64 <= 65536 \/ 65536 + 1196128 <= (V 47%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb6a88 M) (st fx' R' 0xb4cf4 M')
        /\ (forall x, In x KS_abaKd -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 748216
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 24)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 47%nat) + 32)
        /\ getr R' (reg 24) = Z_to_bv 64 1).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G10 G18 G19 G20 G21 G23 G25 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 pvzI9 K15 K16 K17 K18 K19 pvzI10 K21 K22 K23 K24 K25 K26 K27 K28 pvzI11 K30 K31 K32 K33 K34 K35 pvzI12 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K20l; move K20l before pvzI10; pose proof (proj2 pvzI10) as K20r; move K20r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K29l; move K29l before pvzI11; pose proof (proj2 pvzI11) as K29r; move K29r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K36l; move K36l before pvzI12; pose proof (proj2 pvzI12) as K36r; move K36r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PabaKd.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PabaKd.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PabaKd.kn0).
  { unfold know_ok, PabaKd.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | clear; lia | exact K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | clear; lia | exact K30]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | exact (conj K36l K36r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K36l K36r; lia | clear - HV48l HV48r K36l K36r; lia | clear - HV48l HV48r K36l K36r; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K41; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K43; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K44; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K45; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K47; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PabaKd.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PabaKd.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PabaKd.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PabaKd.ps0) with 0xb4cf4 in Hms. change (SR.ps_regs PabaKd.ps0) with (map (fun i => (i, nth i PabaKd.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PabaKd.ps0) with PabaKd.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PabaKd.regs0 PabaKd.regs_out0 72 KS_abaKd KS_abaKd_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PabaKd.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PabaKd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaKd.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PabaKd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaKd.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PabaKd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaKd.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PabaKd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PabaKd.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PabaKd.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PabaKe := BndP_Ea_002S8.LibSegEa_abaKe.
Definition KS_abaKe : list nat := Eval vm_compute in (BG.kept_list 72 PabaKe.regs0 PabaKe.regs_out0).
Lemma KS_abaKe_ok : BG.kept_ok 72 PabaKe.regs0 PabaKe.regs_out0 KS_abaKe = true. Proof. vm_compute. reflexivity. Qed.
Lemma abaKe_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 256 -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 (V 37%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6914048 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 160) + 160 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 160)) -> 6914048 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 160) + 160 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 160)) ->
  6914048 <= (V 37%nat) <= 140737488355320 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 37%nat) 8 -> (((V 2%nat) - 160) + 160 <= (V 37%nat) \/ (V 37%nat) + 8 <= ((V 2%nat) - 160)) -> ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 36%nat)) ->
  ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 38%nat)) -> 6914048 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 64 ->
  L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) ->
  4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) ->
  (((V 2%nat) - 160) + 160 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) ->
  ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 36%nat) / 8) + 2147450880)) -> ((V 38%nat) + 16 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 38%nat)) -> ((V 38%nat) + 16 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 38%nat)) -> ((((V 38%nat) / 8) + 2147450880) + 2 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 38%nat) / 8) + 2147450880)) ->
  ((V 37%nat) + 8 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 37%nat)) -> ((V 37%nat) + 8 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 37%nat)) -> ((((V 37%nat) / 8) + 2147450880) + 1 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 37%nat) / 8) + 2147450880)) -> ((V 47%nat) + 64 <= 65536 \/ 65536 + 1196128 <= (V 47%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb6a88 M) (st fx' R' 0xae310 M')
        /\ (forall x, In x KS_abaKe -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 749228
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G10 G18 G19 G20 G21 G23 G25 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 pvzI9 K15 K16 K17 K18 K19 pvzI10 K21 K22 K23 K24 K25 K26 K27 K28 pvzI11 K30 K31 K32 K33 K34 K35 pvzI12 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K20l; move K20l before pvzI10; pose proof (proj2 pvzI10) as K20r; move K20r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K29l; move K29l before pvzI11; pose proof (proj2 pvzI11) as K29r; move K29r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K36l; move K36l before pvzI12; pose proof (proj2 pvzI12) as K36r; move K36r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PabaKe.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PabaKe.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PabaKe.kn0).
  { unfold know_ok, PabaKe.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | clear; lia | exact K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | clear; lia | exact K30]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | exact (conj K36l K36r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K36l K36r; lia | clear - HV48l HV48r K36l K36r; lia | clear - HV48l HV48r K36l K36r; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K41; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K43; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K44; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K45; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K47; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PabaKe.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PabaKe.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PabaKe.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PabaKe.ps0) with 0xae310 in Hms. change (SR.ps_regs PabaKe.ps0) with (map (fun i => (i, nth i PabaKe.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PabaKe.ps0) with PabaKe.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PabaKe.regs0 PabaKe.regs_out0 72 KS_abaKe KS_abaKe_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PabaKe.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PabaKe.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaKe.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PabaKe.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PabaKe.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PabaKe.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PabaKh := BndP_Ea_002S8.LibSegEa_abaKh.
Definition KS_abaKh : list nat := Eval vm_compute in (BG.kept_list 72 PabaKh.regs0 PabaKh.regs_out0).
Lemma KS_abaKh_ok : BG.kept_ok 72 PabaKh.regs0 PabaKh.regs_out0 KS_abaKh = true. Proof. vm_compute. reflexivity. Qed.
Lemma abaKh_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 35 -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 (V 37%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6914048 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 160) + 160 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 160)) -> 6914048 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 160) + 160 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 160)) ->
  6914048 <= (V 37%nat) <= 140737488355320 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 37%nat) 8 -> (((V 2%nat) - 160) + 160 <= (V 37%nat) \/ (V 37%nat) + 8 <= ((V 2%nat) - 160)) -> ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 36%nat)) ->
  ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 38%nat)) -> 6914048 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 64 ->
  L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) ->
  4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) ->
  (((V 2%nat) - 160) + 160 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) ->
  ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 36%nat) / 8) + 2147450880)) -> ((V 38%nat) + 16 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 38%nat)) -> ((V 38%nat) + 16 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 38%nat)) -> ((((V 38%nat) / 8) + 2147450880) + 2 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 38%nat) / 8) + 2147450880)) ->
  ((V 37%nat) + 8 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 37%nat)) -> ((V 37%nat) + 8 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 37%nat)) -> ((((V 37%nat) / 8) + 2147450880) + 1 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 37%nat) / 8) + 2147450880)) -> ((V 47%nat) + 64 <= 65536 \/ 65536 + 1196128 <= (V 47%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb6a88 M) (st fx' R' 0xb4cf4 M')
        /\ (forall x, In x KS_abaKh -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 748404
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 24)
        /\ getr R' (reg 11) = Z_to_bv 64 1).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G10 G18 G19 G20 G21 G23 G25 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 pvzI9 K15 K16 K17 K18 K19 pvzI10 K21 K22 K23 K24 K25 K26 K27 K28 pvzI11 K30 K31 K32 K33 K34 K35 pvzI12 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K20l; move K20l before pvzI10; pose proof (proj2 pvzI10) as K20r; move K20r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K29l; move K29l before pvzI11; pose proof (proj2 pvzI11) as K29r; move K29r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K36l; move K36l before pvzI12; pose proof (proj2 pvzI12) as K36r; move K36r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PabaKh.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PabaKh.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PabaKh.kn0).
  { unfold know_ok, PabaKh.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | clear; lia | exact K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | clear; lia | exact K30]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | exact (conj K36l K36r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K36l K36r; lia | clear - HV48l HV48r K36l K36r; lia | clear - HV48l HV48r K36l K36r; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K41; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K43; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K44; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K45; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K47; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PabaKh.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PabaKh.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PabaKh.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PabaKh.ps0) with 0xb4cf4 in Hms. change (SR.ps_regs PabaKh.ps0) with (map (fun i => (i, nth i PabaKh.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PabaKh.ps0) with PabaKh.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PabaKh.regs0 PabaKh.regs_out0 72 KS_abaKh KS_abaKh_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PabaKh.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PabaKh.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaKh.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PabaKh.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PabaKh.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PabaKh.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PabaKl := BndP_Ea_002S8.LibSegEa_abaKl.
Definition KS_abaKl : list nat := Eval vm_compute in (BG.kept_list 72 PabaKl.regs0 PabaKl.regs_out0).
Lemma KS_abaKl_ok : BG.kept_ok 72 PabaKl.regs0 PabaKl.regs_out0 KS_abaKl = true. Proof. vm_compute. reflexivity. Qed.
Lemma abaKl_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 39%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 (V 37%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6914048 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 160) + 160 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 160)) -> 6914048 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 160) + 160 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 160)) ->
  6914048 <= (V 37%nat) <= 140737488355320 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 37%nat) 8 -> (((V 2%nat) - 160) + 160 <= (V 37%nat) \/ (V 37%nat) + 8 <= ((V 2%nat) - 160)) -> ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 36%nat)) ->
  ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 38%nat)) -> 6914048 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 64 ->
  L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) ->
  4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) ->
  (((V 2%nat) - 160) + 160 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) ->
  ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 36%nat) / 8) + 2147450880)) -> ((V 38%nat) + 16 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 38%nat)) -> ((V 38%nat) + 16 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 38%nat)) -> ((((V 38%nat) / 8) + 2147450880) + 2 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 38%nat) / 8) + 2147450880)) ->
  ((V 37%nat) + 8 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 37%nat)) -> ((V 37%nat) + 8 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 37%nat)) -> ((((V 37%nat) / 8) + 2147450880) + 1 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 37%nat) / 8) + 2147450880)) -> ((V 47%nat) + 64 <= 65536 \/ 65536 + 1196128 <= (V 47%nat)) ->
  0 <= (V 39%nat) <= 34 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 116) <= bv_unsigned a < ((V 2%nat) - 116) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 116) <= i < ((V 2%nat) - 116) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb6a88 M) (st fx' R' 0xb1990 M')
        /\ (forall x, In x KS_abaKl -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 748540
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 360)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 112)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 116)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 116) 0
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 112) 3).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G18 G19 G20 G21 G23 G25 G26 G27 K0 K1 K2 pvzI8 K4 K5 pvzI9 K7 K8 K9 K10 K11 K12 K13 pvzI10 K15 K16 K17 K18 K19 pvzI11 K21 K22 K23 K24 K25 K26 K27 K28 pvzI12 K30 K31 K32 K33 K34 K35 pvzI13 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 pvzI14.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV47l; move HV47l before pvzI6; pose proof (proj2 pvzI6) as HV47r; move HV47r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV48l; move HV48l before pvzI7; pose proof (proj2 pvzI7) as HV48r; move HV48r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K14l; move K14l before pvzI10; pose proof (proj2 pvzI10) as K14r; move K14r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K20l; move K20l before pvzI11; pose proof (proj2 pvzI11) as K20r; move K20r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K29l; move K29l before pvzI12; pose proof (proj2 pvzI12) as K29r; move K29r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K36l; move K36l before pvzI13; pose proof (proj2 pvzI13) as K36r; move K36r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K52l; move K52l before pvzI14; pose proof (proj2 pvzI14) as K52r; move K52r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PabaKl.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PabaKl.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PabaKl.kn0).
  { unfold know_ok, PabaKl.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | clear; lia | exact K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | clear; lia | exact K30]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | exact (conj K36l K36r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K36l K36r; lia | clear - HV48l HV48r K36l K36r; lia | clear - HV48l HV48r K36l K36r; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K41; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K43; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K44; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K45; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K47; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K52l K52r) | exact (conj K52l K52r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PabaKl.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PabaKl.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 116) <= bv_unsigned a < (vz_2 - 116) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PabaKl.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PabaKl.ps0) with 0xb1990 in Hms. change (SR.ps_regs PabaKl.ps0) with (map (fun i => (i, nth i PabaKl.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PabaKl.ps0) with PabaKl.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PabaKl.regs0 PabaKl.regs_out0 72 KS_abaKl KS_abaKl_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PabaKl.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PabaKl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaKl.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PabaKl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaKl.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PabaKl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaKl.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PabaKl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PabaKu := BndP_Ea_002S8.LibSegEa_abaKu.
Definition KS_abaKu : list nat := Eval vm_compute in (BG.kept_list 72 PabaKu.regs0 PabaKu.regs_out0).
Lemma KS_abaKu_ok : BG.kept_ok 72 PabaKu.regs0 PabaKu.regs_out0 KS_abaKu = true. Proof. vm_compute. reflexivity. Qed.
Lemma abaKu_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 39%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 (V 37%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6914048 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 160) + 160 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 160)) -> 6914048 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 160) + 160 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 160)) ->
  6914048 <= (V 37%nat) <= 140737488355320 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 37%nat) 8 -> (((V 2%nat) - 160) + 160 <= (V 37%nat) \/ (V 37%nat) + 8 <= ((V 2%nat) - 160)) -> ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 36%nat)) ->
  ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 38%nat)) -> 6914048 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 64 ->
  L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) ->
  4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) ->
  (((V 2%nat) - 160) + 160 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) ->
  ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 36%nat) / 8) + 2147450880)) -> ((V 38%nat) + 16 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 38%nat)) -> ((V 38%nat) + 16 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 38%nat)) -> ((((V 38%nat) / 8) + 2147450880) + 2 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 38%nat) / 8) + 2147450880)) ->
  ((V 37%nat) + 8 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 37%nat)) -> ((V 37%nat) + 8 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 37%nat)) -> ((((V 37%nat) / 8) + 2147450880) + 1 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 37%nat) / 8) + 2147450880)) -> ((V 47%nat) + 64 <= 65536 \/ 65536 + 1196128 <= (V 47%nat)) ->
  37 <= (V 39%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 116) <= bv_unsigned a < ((V 2%nat) - 116) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 116) <= i < ((V 2%nat) - 116) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb6a88 M) (st fx' R' 0xb1990 M')
        /\ (forall x, In x KS_abaKu -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 748540
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 360)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 112)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 116)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 116) 0
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 112) 3).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G18 G19 G20 G21 G23 G25 G26 G27 K0 K1 K2 pvzI8 K4 K5 pvzI9 K7 K8 K9 K10 K11 K12 K13 pvzI10 K15 K16 K17 K18 K19 pvzI11 K21 K22 K23 K24 K25 K26 K27 K28 pvzI12 K30 K31 K32 K33 K34 K35 pvzI13 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 pvzI14.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV47l; move HV47l before pvzI6; pose proof (proj2 pvzI6) as HV47r; move HV47r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV48l; move HV48l before pvzI7; pose proof (proj2 pvzI7) as HV48r; move HV48r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K14l; move K14l before pvzI10; pose proof (proj2 pvzI10) as K14r; move K14r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K20l; move K20l before pvzI11; pose proof (proj2 pvzI11) as K20r; move K20r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K29l; move K29l before pvzI12; pose proof (proj2 pvzI12) as K29r; move K29r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K36l; move K36l before pvzI13; pose proof (proj2 pvzI13) as K36r; move K36r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K52l; move K52l before pvzI14; pose proof (proj2 pvzI14) as K52r; move K52r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PabaKu.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PabaKu.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PabaKu.kn0).
  { unfold know_ok, PabaKu.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | clear; lia | exact K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | clear; lia | exact K30]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | exact (conj K36l K36r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K36l K36r; lia | clear - HV48l HV48r K36l K36r; lia | clear - HV48l HV48r K36l K36r; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K41; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K43; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K44; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K45; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K47; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K52l K52r) | exact (conj K52l K52r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PabaKu.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PabaKu.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 116) <= bv_unsigned a < (vz_2 - 116) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PabaKu.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PabaKu.ps0) with 0xb1990 in Hms. change (SR.ps_regs PabaKu.ps0) with (map (fun i => (i, nth i PabaKu.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PabaKu.ps0) with PabaKu.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PabaKu.regs0 PabaKu.regs_out0 72 KS_abaKu KS_abaKu_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PabaKu.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PabaKu.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaKu.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PabaKu.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaKu.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PabaKu.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaKu.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PabaKu.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PabaT1 := BndP_Ea_003S8.LibSegEa_abaT1.
Definition KS_abaT1 : list nat := Eval vm_compute in (BG.kept_list 72 PabaT1.regs0 PabaT1.regs_out0).
Lemma KS_abaT1_ok : BG.kept_ok 72 PabaT1.regs0 PabaT1.regs_out0 KS_abaT1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma abaT1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 (V 37%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 47%nat) + 32) -> getr R (reg 23) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 24) = Z_to_bv 64 1 -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6914048 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 160) + 160 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 160)) -> 6914048 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 160) + 160 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 160)) ->
  6914048 <= (V 37%nat) <= 140737488355320 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 37%nat) 8 -> (((V 2%nat) - 160) + 160 <= (V 37%nat) \/ (V 37%nat) + 8 <= ((V 2%nat) - 160)) -> ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 36%nat)) ->
  ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 38%nat)) -> 6914048 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 64 ->
  L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) ->
  4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) ->
  (((V 2%nat) - 160) + 160 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) ->
  ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 36%nat) / 8) + 2147450880)) -> ((V 38%nat) + 16 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 38%nat)) -> ((V 38%nat) + 16 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 38%nat)) -> ((((V 38%nat) / 8) + 2147450880) + 2 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 38%nat) / 8) + 2147450880)) ->
  ((V 37%nat) + 8 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 37%nat)) -> ((V 37%nat) + 8 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 37%nat)) -> ((((V 37%nat) / 8) + 2147450880) + 1 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 37%nat) / 8) + 2147450880)) -> ((V 47%nat) + 64 <= 65536 \/ 65536 + 1196128 <= (V 47%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((((V 47%nat) / 8) + 2147450880) + 4) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 4) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((((V 47%nat) / 8) + 2147450880) + 4) <= i < ((((V 47%nat) / 8) + 2147450880) + 4) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb6ab8 M) (st fx' R' 0xb540c M')
        /\ (forall x, In x KS_abaT1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 748236
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 24)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 47%nat) + 32)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 1).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 pvzI9 K15 K16 K17 K18 K19 pvzI10 K21 K22 K23 K24 K25 K26 K27 K28 pvzI11 K30 K31 K32 K33 K34 K35 pvzI12 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K20l; move K20l before pvzI10; pose proof (proj2 pvzI10) as K20r; move K20r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K29l; move K29l before pvzI11; pose proof (proj2 pvzI11) as K29r; move K29r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K36l; move K36l before pvzI12; pose proof (proj2 pvzI12) as K36r; move K36r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PabaT1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PabaT1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PabaT1.kn0).
  { unfold know_ok, PabaT1.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | clear; lia | exact K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | clear; lia | exact K30]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | exact (conj K36l K36r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K36l K36r; lia | clear - HV48l HV48r K36l K36r; lia | clear - HV48l HV48r K36l K36r; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K41; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K43; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K44; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K45; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K47; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PabaT1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PabaT1.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((vz_47 / 8) + 2147450880) + 4) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 4) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PabaT1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K29l K29r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PabaT1.ps0) with 0xb540c in Hms. change (SR.ps_regs PabaT1.ps0) with (map (fun i => (i, nth i PabaT1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PabaT1.ps0) with PabaT1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PabaT1.regs0 PabaT1.regs_out0 72 KS_abaT1 KS_abaT1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PabaT1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PabaT1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaT1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PabaT1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaT1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PabaT1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaT1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PabaT1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.

Module PabaT2p := BndP_Ea_003S8.LibSegEa_abaT2p.
Definition KS_abaT2p : list nat := Eval vm_compute in (BG.kept_list 72 PabaT2p.regs0 PabaT2p.regs_out0).
Lemma KS_abaT2p_ok : BG.kept_ok 72 PabaT2p.regs0 PabaT2p.regs_out0 KS_abaT2p = true. Proof. vm_compute. reflexivity. Qed.
Lemma abaT2p_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 1 -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 (V 37%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 47%nat) + 32) -> getr R (reg 23) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 24) = Z_to_bv 64 1 -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6914048 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 160) + 160 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 160)) -> 6914048 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 160) + 160 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 160)) ->
  6914048 <= (V 37%nat) <= 140737488355320 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 37%nat) 8 -> (((V 2%nat) - 160) + 160 <= (V 37%nat) \/ (V 37%nat) + 8 <= ((V 2%nat) - 160)) -> ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 36%nat)) ->
  ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 38%nat)) -> 6914048 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 64 ->
  L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) ->
  4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) ->
  (((V 2%nat) - 160) + 160 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) ->
  ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 36%nat) / 8) + 2147450880)) -> ((V 38%nat) + 16 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 38%nat)) -> ((V 38%nat) + 16 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 38%nat)) -> ((((V 38%nat) / 8) + 2147450880) + 2 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 38%nat) / 8) + 2147450880)) ->
  ((V 37%nat) + 8 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 37%nat)) -> ((V 37%nat) + 8 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 37%nat)) -> ((((V 37%nat) / 8) + 2147450880) + 1 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 37%nat) / 8) + 2147450880)) -> ((V 47%nat) + 64 <= 65536 \/ 65536 + 1196128 <= (V 47%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb6acc M) (st fx' R' 0xb4bd0 M')
        /\ (forall x, In x KS_abaT2p -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 748248
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 24)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 pvzI9 K15 K16 K17 K18 K19 pvzI10 K21 K22 K23 K24 K25 K26 K27 K28 pvzI11 K30 K31 K32 K33 K34 K35 pvzI12 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K20l; move K20l before pvzI10; pose proof (proj2 pvzI10) as K20r; move K20r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K29l; move K29l before pvzI11; pose proof (proj2 pvzI11) as K29r; move K29r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K36l; move K36l before pvzI12; pose proof (proj2 pvzI12) as K36r; move K36r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PabaT2p.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PabaT2p.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PabaT2p.kn0).
  { unfold know_ok, PabaT2p.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | clear; lia | exact K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | clear; lia | exact K30]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | exact (conj K36l K36r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K36l K36r; lia | clear - HV48l HV48r K36l K36r; lia | clear - HV48l HV48r K36l K36r; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K41; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K43; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K44; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K45; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K47; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PabaT2p.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PabaT2p.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PabaT2p.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PabaT2p.ps0) with 0xb4bd0 in Hms. change (SR.ps_regs PabaT2p.ps0) with (map (fun i => (i, nth i PabaT2p.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PabaT2p.ps0) with PabaT2p.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PabaT2p.regs0 PabaT2p.regs_out0 72 KS_abaT2p KS_abaT2p_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PabaT2p.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PabaT2p.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PabaT2p.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PabaT2p.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PabaT2z := BndP_Ea_003S8.LibSegEa_abaT2z.
Definition KS_abaT2z : list nat := Eval vm_compute in (BG.kept_list 72 PabaT2z.regs0 PabaT2z.regs_out0).
Lemma KS_abaT2z_ok : BG.kept_ok 72 PabaT2z.regs0 PabaT2z.regs_out0 KS_abaT2z = true. Proof. vm_compute. reflexivity. Qed.
Lemma abaT2z_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 0 -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 (V 37%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 47%nat) + 32) -> getr R (reg 23) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 24) = Z_to_bv 64 1 -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6914048 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 160) + 160 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 160)) -> 6914048 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 160) + 160 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 160)) ->
  6914048 <= (V 37%nat) <= 140737488355320 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 37%nat) 8 -> (((V 2%nat) - 160) + 160 <= (V 37%nat) \/ (V 37%nat) + 8 <= ((V 2%nat) - 160)) -> ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 36%nat)) ->
  ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 38%nat)) -> 6914048 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 64 ->
  L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) ->
  4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) ->
  (((V 2%nat) - 160) + 160 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) ->
  ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 36%nat) / 8) + 2147450880)) -> ((V 38%nat) + 16 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 38%nat)) -> ((V 38%nat) + 16 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 38%nat)) -> ((((V 38%nat) / 8) + 2147450880) + 2 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 38%nat) / 8) + 2147450880)) ->
  ((V 37%nat) + 8 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 37%nat)) -> ((V 37%nat) + 8 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 37%nat)) -> ((((V 37%nat) / 8) + 2147450880) + 1 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 37%nat) / 8) + 2147450880)) -> ((V 47%nat) + 64 <= 65536 \/ 65536 + 1196128 <= (V 47%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb6acc M) (st fx' R' 0xae310 M')
        /\ (forall x, In x KS_abaT2z -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 748824
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 pvzI9 K15 K16 K17 K18 K19 pvzI10 K21 K22 K23 K24 K25 K26 K27 K28 pvzI11 K30 K31 K32 K33 K34 K35 pvzI12 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K20l; move K20l before pvzI10; pose proof (proj2 pvzI10) as K20r; move K20r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K29l; move K29l before pvzI11; pose proof (proj2 pvzI11) as K29r; move K29r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K36l; move K36l before pvzI12; pose proof (proj2 pvzI12) as K36r; move K36r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PabaT2z.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PabaT2z.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PabaT2z.kn0).
  { unfold know_ok, PabaT2z.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | clear; lia | exact K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | clear; lia | exact K30]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | exact (conj K36l K36r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K36l K36r; lia | clear - HV48l HV48r K36l K36r; lia | clear - HV48l HV48r K36l K36r; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K41; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K43; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K44; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K45; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K47; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PabaT2z.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PabaT2z.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PabaT2z.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PabaT2z.ps0) with 0xae310 in Hms. change (SR.ps_regs PabaT2z.ps0) with (map (fun i => (i, nth i PabaT2z.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PabaT2z.ps0) with PabaT2z.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PabaT2z.regs0 PabaT2z.regs_out0 72 KS_abaT2z KS_abaT2z_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PabaT2z.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PabaT2z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaT2z.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PabaT2z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PabaT2z.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PabaT2z.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PabaT3e := BndP_Ea_003S8.LibSegEa_abaT3e.
Definition KS_abaT3e : list nat := Eval vm_compute in (BG.kept_list 72 PabaT3e.regs0 PabaT3e.regs_out0).
Lemma KS_abaT3e_ok : BG.kept_ok 72 PabaT3e.regs0 PabaT3e.regs_out0 KS_abaT3e = true. Proof. vm_compute. reflexivity. Qed.
Lemma abaT3e_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 256 -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 (V 37%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 47%nat) + 32) -> getr R (reg 23) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 24) = Z_to_bv 64 1 -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6914048 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 160) + 160 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 160)) -> 6914048 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 160) + 160 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 160)) ->
  6914048 <= (V 37%nat) <= 140737488355320 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 37%nat) 8 -> (((V 2%nat) - 160) + 160 <= (V 37%nat) \/ (V 37%nat) + 8 <= ((V 2%nat) - 160)) -> ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 36%nat)) ->
  ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 38%nat)) -> 6914048 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 64 ->
  L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) ->
  4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) ->
  (((V 2%nat) - 160) + 160 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) ->
  ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 36%nat) / 8) + 2147450880)) -> ((V 38%nat) + 16 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 38%nat)) -> ((V 38%nat) + 16 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 38%nat)) -> ((((V 38%nat) / 8) + 2147450880) + 2 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 38%nat) / 8) + 2147450880)) ->
  ((V 37%nat) + 8 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 37%nat)) -> ((V 37%nat) + 8 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 37%nat)) -> ((((V 37%nat) / 8) + 2147450880) + 1 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 37%nat) / 8) + 2147450880)) -> ((V 47%nat) + 64 <= 65536 \/ 65536 + 1196128 <= (V 47%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb6ad8 M) (st fx' R' 0xae310 M')
        /\ (forall x, In x KS_abaT3e -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 748824
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 pvzI9 K15 K16 K17 K18 K19 pvzI10 K21 K22 K23 K24 K25 K26 K27 K28 pvzI11 K30 K31 K32 K33 K34 K35 pvzI12 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K20l; move K20l before pvzI10; pose proof (proj2 pvzI10) as K20r; move K20r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K29l; move K29l before pvzI11; pose proof (proj2 pvzI11) as K29r; move K29r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K36l; move K36l before pvzI12; pose proof (proj2 pvzI12) as K36r; move K36r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PabaT3e.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PabaT3e.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PabaT3e.kn0).
  { unfold know_ok, PabaT3e.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | clear; lia | exact K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | clear; lia | exact K30]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | exact (conj K36l K36r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K36l K36r; lia | clear - HV48l HV48r K36l K36r; lia | clear - HV48l HV48r K36l K36r; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K41; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K43; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K44; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K45; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K47; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PabaT3e.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PabaT3e.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PabaT3e.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PabaT3e.ps0) with 0xae310 in Hms. change (SR.ps_regs PabaT3e.ps0) with (map (fun i => (i, nth i PabaT3e.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PabaT3e.ps0) with PabaT3e.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PabaT3e.regs0 PabaT3e.regs_out0 72 KS_abaT3e KS_abaT3e_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PabaT3e.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PabaT3e.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaT3e.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PabaT3e.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PabaT3e.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PabaT3e.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PabaT3h := BndP_Ea_003S8.LibSegEa_abaT3h.
Definition KS_abaT3h : list nat := Eval vm_compute in (BG.kept_list 72 PabaT3h.regs0 PabaT3h.regs_out0).
Lemma KS_abaT3h_ok : BG.kept_ok 72 PabaT3h.regs0 PabaT3h.regs_out0 KS_abaT3h = true. Proof. vm_compute. reflexivity. Qed.
Lemma abaT3h_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 35 -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 (V 37%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 47%nat) + 32) -> getr R (reg 23) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 24) = Z_to_bv 64 1 -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6914048 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 160) + 160 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 160)) -> 6914048 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 160) + 160 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 160)) ->
  6914048 <= (V 37%nat) <= 140737488355320 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 37%nat) 8 -> (((V 2%nat) - 160) + 160 <= (V 37%nat) \/ (V 37%nat) + 8 <= ((V 2%nat) - 160)) -> ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 36%nat)) ->
  ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 38%nat)) -> 6914048 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 64 ->
  L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) ->
  4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) ->
  (((V 2%nat) - 160) + 160 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) ->
  ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 36%nat) / 8) + 2147450880)) -> ((V 38%nat) + 16 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 38%nat)) -> ((V 38%nat) + 16 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 38%nat)) -> ((((V 38%nat) / 8) + 2147450880) + 2 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 38%nat) / 8) + 2147450880)) ->
  ((V 37%nat) + 8 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 37%nat)) -> ((V 37%nat) + 8 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 37%nat)) -> ((((V 37%nat) / 8) + 2147450880) + 1 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 37%nat) / 8) + 2147450880)) -> ((V 47%nat) + 64 <= 65536 \/ 65536 + 1196128 <= (V 47%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb6ad8 M) (st fx' R' 0xb4cf4 M')
        /\ (forall x, In x KS_abaT3h -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 748280
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 24)
        /\ getr R' (reg 11) = Z_to_bv 64 1).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 pvzI9 K15 K16 K17 K18 K19 pvzI10 K21 K22 K23 K24 K25 K26 K27 K28 pvzI11 K30 K31 K32 K33 K34 K35 pvzI12 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K20l; move K20l before pvzI10; pose proof (proj2 pvzI10) as K20r; move K20r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K29l; move K29l before pvzI11; pose proof (proj2 pvzI11) as K29r; move K29r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K36l; move K36l before pvzI12; pose proof (proj2 pvzI12) as K36r; move K36r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PabaT3h.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PabaT3h.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PabaT3h.kn0).
  { unfold know_ok, PabaT3h.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | clear; lia | exact K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | clear; lia | exact K30]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | exact (conj K36l K36r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K36l K36r; lia | clear - HV48l HV48r K36l K36r; lia | clear - HV48l HV48r K36l K36r; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K41; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K43; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K44; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K45; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K47; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PabaT3h.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PabaT3h.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PabaT3h.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PabaT3h.ps0) with 0xb4cf4 in Hms. change (SR.ps_regs PabaT3h.ps0) with (map (fun i => (i, nth i PabaT3h.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PabaT3h.ps0) with PabaT3h.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PabaT3h.regs0 PabaT3h.regs_out0 72 KS_abaT3h KS_abaT3h_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PabaT3h.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PabaT3h.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaT3h.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PabaT3h.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PabaT3h.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PabaT3h.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PabaT3l := BndP_Ea_003S8.LibSegEa_abaT3l.
Definition KS_abaT3l : list nat := Eval vm_compute in (BG.kept_list 72 PabaT3l.regs0 PabaT3l.regs_out0).
Lemma KS_abaT3l_ok : BG.kept_ok 72 PabaT3l.regs0 PabaT3l.regs_out0 KS_abaT3l = true. Proof. vm_compute. reflexivity. Qed.
Lemma abaT3l_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 39%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 (V 37%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 47%nat) + 32) -> getr R (reg 23) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 24) = Z_to_bv 64 1 -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6914048 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 160) + 160 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 160)) -> 6914048 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 160) + 160 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 160)) ->
  6914048 <= (V 37%nat) <= 140737488355320 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 37%nat) 8 -> (((V 2%nat) - 160) + 160 <= (V 37%nat) \/ (V 37%nat) + 8 <= ((V 2%nat) - 160)) -> ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 36%nat)) ->
  ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 38%nat)) -> 6914048 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 64 ->
  L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) ->
  4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) ->
  (((V 2%nat) - 160) + 160 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) ->
  ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 36%nat) / 8) + 2147450880)) -> ((V 38%nat) + 16 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 38%nat)) -> ((V 38%nat) + 16 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 38%nat)) -> ((((V 38%nat) / 8) + 2147450880) + 2 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 38%nat) / 8) + 2147450880)) ->
  ((V 37%nat) + 8 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 37%nat)) -> ((V 37%nat) + 8 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 37%nat)) -> ((((V 37%nat) / 8) + 2147450880) + 1 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 37%nat) / 8) + 2147450880)) -> ((V 47%nat) + 64 <= 65536 \/ 65536 + 1196128 <= (V 47%nat)) ->
  0 <= (V 39%nat) <= 34 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb6ad8 M) (st fx' R' 0xae310 M')
        /\ (forall x, In x KS_abaT3l -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 748824
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 3
        /\ getr R' (reg 24) = Z_to_bv 64 3).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI8 K4 K5 pvzI9 K7 K8 K9 K10 K11 K12 K13 pvzI10 K15 K16 K17 K18 K19 pvzI11 K21 K22 K23 K24 K25 K26 K27 K28 pvzI12 K30 K31 K32 K33 K34 K35 pvzI13 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 pvzI14.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV47l; move HV47l before pvzI6; pose proof (proj2 pvzI6) as HV47r; move HV47r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV48l; move HV48l before pvzI7; pose proof (proj2 pvzI7) as HV48r; move HV48r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K14l; move K14l before pvzI10; pose proof (proj2 pvzI10) as K14r; move K14r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K20l; move K20l before pvzI11; pose proof (proj2 pvzI11) as K20r; move K20r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K29l; move K29l before pvzI12; pose proof (proj2 pvzI12) as K29r; move K29r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K36l; move K36l before pvzI13; pose proof (proj2 pvzI13) as K36r; move K36r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K52l; move K52l before pvzI14; pose proof (proj2 pvzI14) as K52r; move K52r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PabaT3l.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PabaT3l.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PabaT3l.kn0).
  { unfold know_ok, PabaT3l.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | clear; lia | exact K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | clear; lia | exact K30]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | exact (conj K36l K36r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K36l K36r; lia | clear - HV48l HV48r K36l K36r; lia | clear - HV48l HV48r K36l K36r; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K41; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K43; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K44; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K45; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K47; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K52l K52r) | exact (conj K52l K52r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PabaT3l.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PabaT3l.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PabaT3l.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PabaT3l.ps0) with 0xae310 in Hms. change (SR.ps_regs PabaT3l.ps0) with (map (fun i => (i, nth i PabaT3l.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PabaT3l.ps0) with PabaT3l.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PabaT3l.regs0 PabaT3l.regs_out0 72 KS_abaT3l KS_abaT3l_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PabaT3l.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PabaT3l.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaT3l.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PabaT3l.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaT3l.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PabaT3l.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PabaT3l.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PabaT3l.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PabaT3u := BndP_Ea_003S8.LibSegEa_abaT3u.
Definition KS_abaT3u : list nat := Eval vm_compute in (BG.kept_list 72 PabaT3u.regs0 PabaT3u.regs_out0).
Lemma KS_abaT3u_ok : BG.kept_ok 72 PabaT3u.regs0 PabaT3u.regs_out0 KS_abaT3u = true. Proof. vm_compute. reflexivity. Qed.
Lemma abaT3u_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 39%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 (V 37%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 47%nat) + 32) -> getr R (reg 23) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 24) = Z_to_bv 64 1 -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6914048 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 160) + 160 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 160)) -> 6914048 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 160) + 160 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 160)) ->
  6914048 <= (V 37%nat) <= 140737488355320 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 37%nat) 8 -> (((V 2%nat) - 160) + 160 <= (V 37%nat) \/ (V 37%nat) + 8 <= ((V 2%nat) - 160)) -> ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 36%nat)) ->
  ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 38%nat)) -> 6914048 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 64 ->
  L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) ->
  4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) ->
  (((V 2%nat) - 160) + 160 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) ->
  ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 36%nat) / 8) + 2147450880)) -> ((V 38%nat) + 16 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 38%nat)) -> ((V 38%nat) + 16 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 38%nat)) -> ((((V 38%nat) / 8) + 2147450880) + 2 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 38%nat) / 8) + 2147450880)) ->
  ((V 37%nat) + 8 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 37%nat)) -> ((V 37%nat) + 8 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 37%nat)) -> ((((V 37%nat) / 8) + 2147450880) + 1 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 37%nat) / 8) + 2147450880)) -> ((V 47%nat) + 64 <= 65536 \/ 65536 + 1196128 <= (V 47%nat)) ->
  36 <= (V 39%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb6ad8 M) (st fx' R' 0xae310 M')
        /\ (forall x, In x KS_abaT3u -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 748824
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 3
        /\ getr R' (reg 24) = Z_to_bv 64 3).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI8 K4 K5 pvzI9 K7 K8 K9 K10 K11 K12 K13 pvzI10 K15 K16 K17 K18 K19 pvzI11 K21 K22 K23 K24 K25 K26 K27 K28 pvzI12 K30 K31 K32 K33 K34 K35 pvzI13 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 pvzI14.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV47l; move HV47l before pvzI6; pose proof (proj2 pvzI6) as HV47r; move HV47r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV48l; move HV48l before pvzI7; pose proof (proj2 pvzI7) as HV48r; move HV48r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K14l; move K14l before pvzI10; pose proof (proj2 pvzI10) as K14r; move K14r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K20l; move K20l before pvzI11; pose proof (proj2 pvzI11) as K20r; move K20r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K29l; move K29l before pvzI12; pose proof (proj2 pvzI12) as K29r; move K29r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K36l; move K36l before pvzI13; pose proof (proj2 pvzI13) as K36r; move K36r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K52l; move K52l before pvzI14; pose proof (proj2 pvzI14) as K52r; move K52r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PabaT3u.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PabaT3u.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PabaT3u.kn0).
  { unfold know_ok, PabaT3u.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | clear; lia | exact K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | clear; lia | exact K30]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | exact (conj K36l K36r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K36l K36r; lia | clear - HV48l HV48r K36l K36r; lia | clear - HV48l HV48r K36l K36r; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K41; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K43; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K44; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K45; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K47; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K52l K52r) | exact (conj K52l K52r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PabaT3u.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PabaT3u.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PabaT3u.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PabaT3u.ps0) with 0xae310 in Hms. change (SR.ps_regs PabaT3u.ps0) with (map (fun i => (i, nth i PabaT3u.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PabaT3u.ps0) with PabaT3u.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PabaT3u.regs0 PabaT3u.regs_out0 72 KS_abaT3u KS_abaT3u_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PabaT3u.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PabaT3u.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaT3u.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PabaT3u.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaT3u.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PabaT3u.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PabaT3u.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PabaT3u.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PabaT4 := BndP_Ea_003S8.LibSegEa_abaT4.
Definition KS_abaT4 : list nat := Eval vm_compute in (BG.kept_list 72 PabaT4.regs0 PabaT4.regs_out0).
Lemma KS_abaT4_ok : BG.kept_ok 72 PabaT4.regs0 PabaT4.regs_out0 KS_abaT4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma abaT4_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 (V 37%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 47%nat) + 32) -> getr R (reg 23) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 24) = Z_to_bv 64 1 -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6914048 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 160) + 160 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 160)) -> 6914048 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 160) + 160 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 160)) ->
  6914048 <= (V 37%nat) <= 140737488355320 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 37%nat) 8 -> (((V 2%nat) - 160) + 160 <= (V 37%nat) \/ (V 37%nat) + 8 <= ((V 2%nat) - 160)) -> ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 36%nat)) ->
  ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 38%nat)) -> 6914048 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 64 ->
  L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) ->
  4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) ->
  (((V 2%nat) - 160) + 160 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) ->
  ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 36%nat) / 8) + 2147450880)) -> ((V 38%nat) + 16 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 38%nat)) -> ((V 38%nat) + 16 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 38%nat)) -> ((((V 38%nat) / 8) + 2147450880) + 2 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 38%nat) / 8) + 2147450880)) ->
  ((V 37%nat) + 8 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 37%nat)) -> ((V 37%nat) + 8 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 37%nat)) -> ((((V 37%nat) / 8) + 2147450880) + 1 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 37%nat) / 8) + 2147450880)) -> ((V 47%nat) + 64 <= 65536 \/ 65536 + 1196128 <= (V 47%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb6af8 M) (st fx' R' 0xb5f04 M')
        /\ (forall x, In x KS_abaT4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 748292
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 38%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 pvzI9 K15 K16 K17 K18 K19 pvzI10 K21 K22 K23 K24 K25 K26 K27 K28 pvzI11 K30 K31 K32 K33 K34 K35 pvzI12 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K20l; move K20l before pvzI10; pose proof (proj2 pvzI10) as K20r; move K20r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K29l; move K29l before pvzI11; pose proof (proj2 pvzI11) as K29r; move K29r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K36l; move K36l before pvzI12; pose proof (proj2 pvzI12) as K36r; move K36r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PabaT4.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PabaT4.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PabaT4.kn0).
  { unfold know_ok, PabaT4.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | clear; lia | exact K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | clear; lia | exact K30]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | exact (conj K36l K36r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K36l K36r; lia | clear - HV48l HV48r K36l K36r; lia | clear - HV48l HV48r K36l K36r; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K41; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K43; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K44; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K45; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K47; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PabaT4.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PabaT4.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PabaT4.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PabaT4.ps0) with 0xb5f04 in Hms. change (SR.ps_regs PabaT4.ps0) with (map (fun i => (i, nth i PabaT4.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PabaT4.ps0) with PabaT4.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PabaT4.regs0 PabaT4.regs_out0 72 KS_abaT4 KS_abaT4_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PabaT4.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PabaT4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabaT4.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PabaT4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PabaT4.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PabaT4.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

End PEABAP1.
