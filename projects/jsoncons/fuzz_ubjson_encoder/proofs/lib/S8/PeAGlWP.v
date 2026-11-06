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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.seg Require BndP_Ea_025S8 BndP_Ea_024S8 BndP_Ea_023S8.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEAGLWP.
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

Module PaglWi := BndP_Ea_025S8.LibSegEa_aglWi.
Definition KS_aglWi : list nat := Eval vm_compute in (BG.kept_list 80 PaglWi.regs0 PaglWi.regs_out0).
Lemma KS_aglWi_ok : BG.kept_ok 80 PaglWi.regs0 PaglWi.regs_out0 KS_aglWi = true. Proof. vm_compute. reflexivity. Qed.
Lemma aglWi_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 1 -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 22) = Z_to_bv 64 1 -> getr R (reg 23) = Z_to_bv 64 ((V 47%nat) + 48) -> getr R (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  6914048 <= (V 47%nat) <= 140737488355072 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 256 -> L5.writable RSEGS M (V 47%nat) 256 ->
  (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 256 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 32 -> L5.u64_at RSEGS M ((V 47%nat) + 248) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 ->
  L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 256 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 256 <= ((V 2%nat) - 128)) ->
  (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) -> L5.u64_at RSEGS M ((V 47%nat) + 48) (V 50%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb6094 M) (st fx' R' 0xb609c M')
        /\ (forall x, In x KS_aglWi -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | 48%nat => Z_to_bv 64 (V 48%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 50))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 pvzI7 K1 K2 K3 K4 K5 K6 pvzI8 K8 K9 K10 K11 K12 K13.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV48l; move HV48l before pvzI5; pose proof (proj2 pvzI5) as HV48r; move HV48r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV50l; move HV50l before pvzI6; pose proof (proj2 pvzI6) as HV50r; move HV50r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K7l; move K7l before pvzI8; pose proof (proj2 pvzI8) as K7r; move K7r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PaglWi.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaglWi.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaglWi.kn0).
  { unfold know_ok, PaglWi.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | generalize K4; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K7l K7r K9 K10 K12; lia | clear - HV48l HV48r K7l K7r K9 K10 K12; lia | clear - HV48l HV48r K7l K7r K9 K10 K12; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K11 K12) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K11 K12) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | exactA K13]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaglWi.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaglWi.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PaglWi.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaglWi.ps0) with 0xb609c in Hms. change (SR.ps_regs PaglWi.ps0) with (map (fun i => (i, nth i PaglWi.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaglWi.ps0) with PaglWi.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaglWi.regs0 PaglWi.regs_out0 80 KS_aglWi KS_aglWi_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg PaglWi.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaglWi.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity.
Qed.

Module PaglWU := BndP_Ea_025S8.LibSegEa_aglWU.
Definition KS_aglWU : list nat := Eval vm_compute in (BG.kept_list 80 PaglWU.regs0 PaglWU.regs_out0).
Lemma KS_aglWU_ok : BG.kept_ok 80 PaglWU.regs0 PaglWU.regs_out0 KS_aglWU = true. Proof. vm_compute. reflexivity. Qed.
Lemma aglWU_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 1 -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 22) = Z_to_bv 64 ((V 47%nat) + 64) -> getr R (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6914048 <= (V 47%nat) <= 140737488355072 ->
  aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 256 -> L5.writable RSEGS M (V 47%nat) 256 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 256 <= 2147446784) ->
  L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 32 -> L5.u64_at RSEGS M ((V 47%nat) + 248) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 256 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 256 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  L5.u64_at RSEGS M ((V 47%nat) + 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 64%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 66%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 68%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 70%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 72%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 73%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 74%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 96) (V 75%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 32) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 32) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb61c8 M) (st fx' R' 0xb63c0 M')
        /\ (forall x, In x KS_aglWU -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 10) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | 48%nat => Z_to_bv 64 (V 48%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | 64%nat => Z_to_bv 64 (V 64%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 66%nat => Z_to_bv 64 (V 66%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | 69%nat => Z_to_bv 64 (V 69%nat) | 70%nat => Z_to_bv 64 (V 70%nat) | 71%nat => Z_to_bv 64 (V 71%nat) | 72%nat => Z_to_bv 64 (V 72%nat) | 73%nat => Z_to_bv 64 (V 73%nat) | 74%nat => Z_to_bv 64 (V 74%nat) | 75%nat => Z_to_bv 64 (V 75%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt false 0 1 (EVar 50))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 69%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 70%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 71%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 74%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 75%nat)
        /\ L5.u8_at RSEGS M' (V 48%nat) 0
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450907) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450906) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450905) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450904) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450911) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450910) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450909) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450908) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450899) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450898) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450897) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450896) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450903) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450902) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450901) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450900) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450891) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450890) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450889) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450888) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450895) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450894) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450893) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450892) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450883) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450882) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450881) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450880) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450887) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450885) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 245
        /\ L5.u64_at RSEGS M' (V 47%nat) 1172321806
        /\ L5.defined M' ((V 47%nat) + 8) 248).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 G2 G8 G9 G10 G18 G19 G20 G21 G22 G24 G25 G26 pvzI19 K1 K2 pvzI20 K4 K5 K6 K7 K8 K9 pvzI21 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV48l; move HV48l before pvzI5; pose proof (proj2 pvzI5) as HV48r; move HV48r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV50l; move HV50l before pvzI6; pose proof (proj2 pvzI6) as HV50r; move HV50r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV64l; move HV64l before pvzI7; pose proof (proj2 pvzI7) as HV64r; move HV64r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV65l; move HV65l before pvzI8; pose proof (proj2 pvzI8) as HV65r; move HV65r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV66l; move HV66l before pvzI9; pose proof (proj2 pvzI9) as HV66r; move HV66r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV67l; move HV67l before pvzI10; pose proof (proj2 pvzI10) as HV67r; move HV67r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV68l; move HV68l before pvzI11; pose proof (proj2 pvzI11) as HV68r; move HV68r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV69l; move HV69l before pvzI12; pose proof (proj2 pvzI12) as HV69r; move HV69r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV70l; move HV70l before pvzI13; pose proof (proj2 pvzI13) as HV70r; move HV70r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV71l; move HV71l before pvzI14; pose proof (proj2 pvzI14) as HV71r; move HV71r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV72l; move HV72l before pvzI15; pose proof (proj2 pvzI15) as HV72r; move HV72r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV73l; move HV73l before pvzI16; pose proof (proj2 pvzI16) as HV73r; move HV73r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV74l; move HV74l before pvzI17; pose proof (proj2 pvzI17) as HV74r; move HV74r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV75l; move HV75l before pvzI18; pose proof (proj2 pvzI18) as HV75r; move HV75r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K0l; move K0l before pvzI19; pose proof (proj2 pvzI19) as K0r; move K0r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K3l; move K3l before pvzI20; pose proof (proj2 pvzI20) as K3r; move K3r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K10l; move K10l before pvzI21; pose proof (proj2 pvzI21) as K10r; move K10r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *. set (vz_73 := V 73%nat) in *. set (vz_74 := V 74%nat) in *. set (vz_75 := V 75%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 50%nat => Z_to_bv 64 vz_50 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | 73%nat => Z_to_bv 64 vz_73 | 74%nat => Z_to_bv 64 vz_74 | 75%nat => Z_to_bv 64 vz_75 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 50%nat => vz_50 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | 73%nat => vz_73 | 74%nat => vz_74 | 75%nat => vz_75 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 76%nat. }
  assert (HR: regs_ok E PaglWU.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaglWU.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaglWU.kn0).
  { unfold know_ok, PaglWU.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K10l K10r K12 K13 K15; lia | clear - HV48l HV48r K10l K10r K12 K13 K15; lia | clear - HV48l HV48r K10l K10r K12 K13 K15; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV73l HV73r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV74l HV74r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV75l HV75r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K28]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaglWU.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaglWU.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 32) -> ~ ((vz_48 + 0) <= bv_unsigned a < (vz_48 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PaglWU.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K3l K3r K7 K13 K14 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K3l K3r K7 K13 K14 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | evalEk' ZA Hag ltac:(clear) | clear - HV48l HV48r K10l K10r K12 K13 K15 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaglWU.ps0) with 0xb63c0 in Hms. change (SR.ps_regs PaglWU.ps0) with (map (fun i => (i, nth i PaglWU.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaglWU.ps0) with PaglWU.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaglWU.regs0 PaglWU.regs_out0 80 KS_aglWU KS_aglWU_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaglWU.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaglWU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglWU.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaglWU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglWU.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaglWU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglWU.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PaglWU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglWU.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaglWU.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
  split. { rewrite (BG.out_reg PaglWU.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaglWU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglWU.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaglWU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglWU.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaglWU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglWU.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PaglWU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglWU.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PaglWU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglWU.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PaglWU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglWU.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PaglWU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglWU.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PaglWU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglWU.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PaglWU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglWU.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PaglWU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 23%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 24%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 25%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 26%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 27%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 28%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 29%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 30%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 31%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 32%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 33%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 34%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PaglWI := BndP_Ea_025S8.LibSegEa_aglWI.
Definition KS_aglWI : list nat := Eval vm_compute in (BG.kept_list 80 PaglWI.regs0 PaglWI.regs_out0).
Lemma KS_aglWI_ok : BG.kept_ok 80 PaglWI.regs0 PaglWI.regs_out0 KS_aglWI = true. Proof. vm_compute. reflexivity. Qed.
Lemma aglWI_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 2 -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 22) = Z_to_bv 64 ((V 47%nat) + 80) -> getr R (reg 23) = Z_to_bv 64 2 -> getr R (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  6914048 <= (V 47%nat) <= 140737488355072 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 256 -> L5.writable RSEGS M (V 47%nat) 256 ->
  (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 256 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 32 -> L5.u64_at RSEGS M ((V 47%nat) + 248) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 ->
  L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 256 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 256 <= ((V 2%nat) - 128)) ->
  (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) -> L5.u64_at RSEGS M ((V 47%nat) + 80) (V 50%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb6248 M) (st fx' R' 0xb625c M')
        /\ (forall x, In x KS_aglWI -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | 48%nat => Z_to_bv 64 (V 48%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EMd Instr.M_MUL (ELit 72058693549555712) (EExt false 0 2 (EVar 50)))
        /\ getr R' (reg 11) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | 48%nat => Z_to_bv 64 (V 48%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EMd Instr.M_MUL (ELit 1099511627776) (EExt false 0 2 (EVar 50)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 pvzI7 K1 K2 K3 K4 K5 K6 pvzI8 K8 K9 K10 K11 K12 K13.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV48l; move HV48l before pvzI5; pose proof (proj2 pvzI5) as HV48r; move HV48r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV50l; move HV50l before pvzI6; pose proof (proj2 pvzI6) as HV50r; move HV50r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K7l; move K7l before pvzI8; pose proof (proj2 pvzI8) as K7r; move K7r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PaglWI.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaglWI.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaglWI.kn0).
  { unfold know_ok, PaglWI.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | generalize K4; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K7l K7r K9 K10 K12; lia | clear - HV48l HV48r K7l K7r K9 K10 K12; lia | clear - HV48l HV48r K7l K7r K9 K10 K12; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K11 K12) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K11 K12) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | exactA K13]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaglWI.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaglWI.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PaglWI.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaglWI.ps0) with 0xb625c in Hms. change (SR.ps_regs PaglWI.ps0) with (map (fun i => (i, nth i PaglWI.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaglWI.ps0) with PaglWI.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaglWI.regs0 PaglWI.regs_out0 80 KS_aglWI KS_aglWI_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaglWI.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaglWI.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
  rewrite (BG.out_reg PaglWI.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaglWI.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity.
Qed.

Module PaglWl := BndP_Ea_025S8.LibSegEa_aglWl.
Definition KS_aglWl : list nat := Eval vm_compute in (BG.kept_list 80 PaglWl.regs0 PaglWl.regs_out0).
Lemma KS_aglWl_ok : BG.kept_ok 80 PaglWl.regs0 PaglWl.regs_out0 KS_aglWl = true. Proof. vm_compute. reflexivity. Qed.
Lemma aglWl_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 4 -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 22) = Z_to_bv 64 4 -> getr R (reg 23) = Z_to_bv 64 ((V 47%nat) + 96) -> getr R (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  6914048 <= (V 47%nat) <= 140737488355072 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 256 -> L5.writable RSEGS M (V 47%nat) 256 ->
  (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 256 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 32 -> L5.u64_at RSEGS M ((V 47%nat) + 248) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 ->
  L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 256 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 256 <= ((V 2%nat) - 128)) ->
  (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) -> L5.u64_at RSEGS M ((V 47%nat) + 96) (V 50%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb61f0 M) (st fx' R' 0xb6224 M')
        /\ (forall x, In x KS_aglWl -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | 48%nat => Z_to_bv 64 (V 48%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_OR (EAlu Instr.ALU_OR (EAluw Instr.ALU_SLL (EExt true 0 4 (EVar 50)) (ELit 24)) (EMd Instr.M_MUL (ELit 256) (EAlu Instr.ALU_AND (EExt true 0 4 (EVar 50)) (ELit 65280)))) (EAlu Instr.ALU_OR (EAlu Instr.ALU_AND (EAlu Instr.ALU_SRL (EExt true 0 4 (EVar 50)) (ELit 8)) (ELit 65280)) (EAluw Instr.ALU_SRL (EExt true 0 4 (EVar 50)) (ELit 24))))
        /\ getr R' (reg 11) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | 48%nat => Z_to_bv 64 (V 48%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EMd Instr.M_MUL (ELit 256) (EAlu Instr.ALU_AND (EExt true 0 4 (EVar 50)) (ELit 65280)))
        /\ getr R' (reg 12) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | 48%nat => Z_to_bv 64 (V 48%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_OR (EAlu Instr.ALU_AND (EAlu Instr.ALU_SRL (EExt true 0 4 (EVar 50)) (ELit 8)) (ELit 65280)) (EAluw Instr.ALU_SRL (EExt true 0 4 (EVar 50)) (ELit 24)))
        /\ getr R' (reg 13) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | 48%nat => Z_to_bv 64 (V 48%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAluw Instr.ALU_SRL (EExt true 0 4 (EVar 50)) (ELit 24))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 pvzI7 K1 K2 K3 K4 K5 K6 pvzI8 K8 K9 K10 K11 K12 K13.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV48l; move HV48l before pvzI5; pose proof (proj2 pvzI5) as HV48r; move HV48r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV50l; move HV50l before pvzI6; pose proof (proj2 pvzI6) as HV50r; move HV50r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K7l; move K7l before pvzI8; pose proof (proj2 pvzI8) as K7r; move K7r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PaglWl.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaglWl.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaglWl.kn0).
  { unfold know_ok, PaglWl.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | generalize K4; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K7l K7r K9 K10 K12; lia | clear - HV48l HV48r K7l K7r K9 K10 K12; lia | clear - HV48l HV48r K7l K7r K9 K10 K12; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K11 K12) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K11 K12) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | exactA K13]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaglWl.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaglWl.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PaglWl.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaglWl.ps0) with 0xb6224 in Hms. change (SR.ps_regs PaglWl.ps0) with (map (fun i => (i, nth i PaglWl.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaglWl.ps0) with PaglWl.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaglWl.regs0 PaglWl.regs_out0 80 KS_aglWl KS_aglWl_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaglWl.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaglWl.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
  split. { rewrite (BG.out_reg PaglWl.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaglWl.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
  split. { rewrite (BG.out_reg PaglWl.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PaglWl.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
  rewrite (BG.out_reg PaglWl.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PaglWl.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity.
Qed.

Module PaglWL := BndP_Ea_025S8.LibSegEa_aglWL.
Definition KS_aglWL : list nat := Eval vm_compute in (BG.kept_list 80 PaglWL.regs0 PaglWL.regs_out0).
Lemma KS_aglWL_ok : BG.kept_ok 80 PaglWL.regs0 PaglWL.regs_out0 KS_aglWL = true. Proof. vm_compute. reflexivity. Qed.
Lemma aglWL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 8 -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 22) = Z_to_bv 64 ((V 47%nat) + 112) -> getr R (reg 23) = Z_to_bv 64 8 -> getr R (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  6914048 <= (V 47%nat) <= 140737488355072 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 256 -> L5.writable RSEGS M (V 47%nat) 256 ->
  (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 256 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 32 -> L5.u64_at RSEGS M ((V 47%nat) + 248) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 ->
  L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 256 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 256 <= ((V 2%nat) - 128)) ->
  (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) -> L5.u64_at RSEGS M ((V 47%nat) + 112) (V 50%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb6134 M) (st fx' R' 0xb61a0 M')
        /\ (forall x, In x KS_aglWL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | 48%nat => Z_to_bv 64 (V 48%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_OR (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 50)) (EMd Instr.M_MUL (ELit 1099511627776) (EAlu Instr.ALU_AND (EVar 50) (ELit 65280)))) (EAlu Instr.ALU_OR (EMd Instr.M_MUL (ELit 16777216) (EAlu Instr.ALU_AND (EVar 50) (ELit 16711680))) (EMd Instr.M_MUL (ELit 4294967296) (EAluw Instr.ALU_SRL (EVar 50) (ELit 24))))) (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EAlu Instr.ALU_AND (EAlu Instr.ALU_SRL (EVar 50) (ELit 24)) (ELit 16711680)) (EMd Instr.M_MUL (ELit 16777216) (EAluw Instr.ALU_SRL (EAlu Instr.ALU_SRL (EVar 50) (ELit 8)) (ELit 24)))) (EAlu Instr.ALU_OR (EAlu Instr.ALU_AND (EAlu Instr.ALU_SRL (EVar 50) (ELit 40)) (ELit 65280)) (EAlu Instr.ALU_SRL (EVar 50) (ELit 56)))))
        /\ bv_unsigned (getr R' (reg 11)) = (Z.land ((V 50%nat) / 16777216) 16711680)
        /\ getr R' (reg 12) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | 48%nat => Z_to_bv 64 (V 48%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 50)) (EMd Instr.M_MUL (ELit 1099511627776) (EAlu Instr.ALU_AND (EVar 50) (ELit 65280)))) (EAlu Instr.ALU_OR (EMd Instr.M_MUL (ELit 16777216) (EAlu Instr.ALU_AND (EVar 50) (ELit 16711680))) (EMd Instr.M_MUL (ELit 4294967296) (EAluw Instr.ALU_SRL (EVar 50) (ELit 24)))))
        /\ getr R' (reg 13) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | 48%nat => Z_to_bv 64 (V 48%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_OR (EMd Instr.M_MUL (ELit 16777216) (EAlu Instr.ALU_AND (EVar 50) (ELit 16711680))) (EMd Instr.M_MUL (ELit 4294967296) (EAluw Instr.ALU_SRL (EVar 50) (ELit 24))))
        /\ bv_unsigned (getr R' (reg 14)) = (Z.lor (Z.land ((V 50%nat) / 1099511627776) 65280) ((V 50%nat) / 72057594037927936))
        /\ bv_unsigned (getr R' (reg 15)) = (Z.land ((V 50%nat) / 1099511627776) 65280)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 pvzI7 K1 K2 K3 K4 K5 K6 pvzI8 K8 K9 K10 K11 K12 K13.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV48l; move HV48l before pvzI5; pose proof (proj2 pvzI5) as HV48r; move HV48r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV50l; move HV50l before pvzI6; pose proof (proj2 pvzI6) as HV50r; move HV50r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K7l; move K7l before pvzI8; pose proof (proj2 pvzI8) as K7r; move K7r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PaglWL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaglWL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaglWL.kn0).
  { unfold know_ok, PaglWL.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | generalize K4; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K7l K7r K9 K10 K12; lia | clear - HV48l HV48r K7l K7r K9 K10 K12; lia | clear - HV48l HV48r K7l K7r K9 K10 K12; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K11 K12) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K11 K12) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K7l K7r K9 K10 K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K0l K0r K4 K10 K11) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | clear - HV47l HV47r K0l K0r K4 K10 K11; lia | exactA K13]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaglWL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaglWL.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PaglWL.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaglWL.ps0) with 0xb61a0 in Hms. change (SR.ps_regs PaglWL.ps0) with (map (fun i => (i, nth i PaglWL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaglWL.ps0) with PaglWL.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaglWL.regs0 PaglWL.regs_out0 80 KS_aglWL KS_aglWL_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaglWL.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaglWL.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
  split. { rewrite (BG.out_reg PaglWL.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaglWL.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
  split. { rewrite (BG.out_reg PaglWL.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PaglWL.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
  split. { rewrite (BG.out_reg PaglWL.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PaglWL.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
  split. { rewrite (BG.out_reg PaglWL.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PaglWL.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
  rewrite (BG.out_reg PaglWL.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PaglWL.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac.
Qed.

Module PaglSiP := BndP_Ea_024S8.LibSegEa_aglSiP.
Definition KS_aglSiP : list nat := Eval vm_compute in (BG.kept_list 80 PaglSiP.regs0 PaglSiP.regs_out0).
Lemma KS_aglSiP_ok : BG.kept_ok 80 PaglSiP.regs0 PaglSiP.regs_out0 KS_aglSiP = true. Proof. vm_compute. reflexivity. Qed.
Lemma aglSiP_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 49%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 22) = Z_to_bv 64 1 -> getr R (reg 23) = Z_to_bv 64 ((V 47%nat) + 48) -> getr R (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6914048 <= (V 47%nat) <= 140737488355072 ->
  aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 256 -> L5.writable RSEGS M (V 47%nat) 256 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 256 <= 2147446784) ->
  L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 32 -> L5.u64_at RSEGS M ((V 47%nat) + 248) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 256 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 256 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 64%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 67%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 68%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 71%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 72) (V 72%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 73%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 74%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 75%nat) ->
  0 <= (V 49%nat) <= 9223372036854775807 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 32) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 32) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb609c M) (st fx' R' 0xb63c0 M')
        /\ (forall x, In x KS_aglSiP -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 69%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 70%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 71%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 74%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 75%nat)
        /\ L5.u8_at RSEGS M' (V 48%nat) 0
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450907) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450906) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450905) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450904) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450911) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450910) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450909) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450908) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450899) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450898) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450897) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450896) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450903) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450902) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450901) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450900) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450891) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450890) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450889) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450888) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450895) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450894) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450893) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450892) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450883) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450882) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450881) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450880) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450887) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450885) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 245
        /\ L5.u64_at RSEGS M' (V 47%nat) 1172321806
        /\ L5.defined M' ((V 47%nat) + 8) 248).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 pvzI19 K1 K2 pvzI20 K4 K5 K6 K7 K8 K9 pvzI21 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 pvzI22.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV48l; move HV48l before pvzI5; pose proof (proj2 pvzI5) as HV48r; move HV48r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV49l; move HV49l before pvzI6; pose proof (proj2 pvzI6) as HV49r; move HV49r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV64l; move HV64l before pvzI7; pose proof (proj2 pvzI7) as HV64r; move HV64r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV65l; move HV65l before pvzI8; pose proof (proj2 pvzI8) as HV65r; move HV65r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV66l; move HV66l before pvzI9; pose proof (proj2 pvzI9) as HV66r; move HV66r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV67l; move HV67l before pvzI10; pose proof (proj2 pvzI10) as HV67r; move HV67r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV68l; move HV68l before pvzI11; pose proof (proj2 pvzI11) as HV68r; move HV68r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV69l; move HV69l before pvzI12; pose proof (proj2 pvzI12) as HV69r; move HV69r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV70l; move HV70l before pvzI13; pose proof (proj2 pvzI13) as HV70r; move HV70r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV71l; move HV71l before pvzI14; pose proof (proj2 pvzI14) as HV71r; move HV71r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV72l; move HV72l before pvzI15; pose proof (proj2 pvzI15) as HV72r; move HV72r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV73l; move HV73l before pvzI16; pose proof (proj2 pvzI16) as HV73r; move HV73r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV74l; move HV74l before pvzI17; pose proof (proj2 pvzI17) as HV74r; move HV74r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV75l; move HV75l before pvzI18; pose proof (proj2 pvzI18) as HV75r; move HV75r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K0l; move K0l before pvzI19; pose proof (proj2 pvzI19) as K0r; move K0r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K3l; move K3l before pvzI20; pose proof (proj2 pvzI20) as K3r; move K3r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K10l; move K10l before pvzI21; pose proof (proj2 pvzI21) as K10r; move K10r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K28l; move K28l before pvzI22; pose proof (proj2 pvzI22) as K28r; move K28r before pvzI22; clear pvzI22.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *. set (vz_73 := V 73%nat) in *. set (vz_74 := V 74%nat) in *. set (vz_75 := V 75%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | 73%nat => Z_to_bv 64 vz_73 | 74%nat => Z_to_bv 64 vz_74 | 75%nat => Z_to_bv 64 vz_75 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | 73%nat => vz_73 | 74%nat => vz_74 | 75%nat => vz_75 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 76%nat. }
  assert (HR: regs_ok E PaglSiP.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaglSiP.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaglSiP.kn0).
  { unfold know_ok, PaglSiP.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K10l K10r K12 K13 K15; lia | clear - HV48l HV48r K10l K10r K12 K13 K15; lia | clear - HV48l HV48r K10l K10r K12 K13 K15; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV73l HV73r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV74l HV74r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV75l HV75r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV49l HV49r K28l K28r) | exact (conj K28l K28r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaglSiP.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaglSiP.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 32) -> ~ ((vz_48 + 0) <= bv_unsigned a < (vz_48 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PaglSiP.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K3l K3r K7 K13 K14 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K3l K3r K7 K13 K14 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | evalEk' ZA Hag ltac:(clear) | clear - HV48l HV48r K10l K10r K12 K13 K15 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaglSiP.ps0) with 0xb63c0 in Hms. change (SR.ps_regs PaglSiP.ps0) with (map (fun i => (i, nth i PaglSiP.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaglSiP.ps0) with PaglSiP.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaglSiP.regs0 PaglSiP.regs_out0 80 KS_aglSiP KS_aglSiP_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaglSiP.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaglSiP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSiP.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaglSiP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSiP.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaglSiP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSiP.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PaglSiP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSiP.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaglSiP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSiP.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaglSiP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSiP.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaglSiP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSiP.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PaglSiP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSiP.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PaglSiP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSiP.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PaglSiP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSiP.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PaglSiP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSiP.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PaglSiP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSiP.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PaglSiP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSiP.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PaglSiP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 23%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 24%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 25%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 26%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 27%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 28%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 29%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 30%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 31%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 32%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 33%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 34%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PaglSIP := BndP_Ea_023S8.LibSegEa_aglSIP.
Definition KS_aglSIP : list nat := Eval vm_compute in (BG.kept_list 80 PaglSIP.regs0 PaglSIP.regs_out0).
Lemma KS_aglSIP_ok : BG.kept_ok 80 PaglSIP.regs0 PaglSIP.regs_out0 KS_aglSIP = true. Proof. vm_compute. reflexivity. Qed.
Lemma aglSIP_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 49%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 22) = Z_to_bv 64 ((V 47%nat) + 80) -> getr R (reg 23) = Z_to_bv 64 2 -> getr R (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6914048 <= (V 47%nat) <= 140737488355072 ->
  aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 256 -> L5.writable RSEGS M (V 47%nat) 256 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 256 <= 2147446784) ->
  L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 32 -> L5.u64_at RSEGS M ((V 47%nat) + 248) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 256 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 256 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 64%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 67%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 68%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 71%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 72) (V 72%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 73%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 74%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 75%nat) ->
  0 <= (V 49%nat) <= 9223372036854775807 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 32) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 32) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb625c M) (st fx' R' 0xb63c0 M')
        /\ (forall x, In x KS_aglSIP -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 10) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | 48%nat => Z_to_bv 64 (V 48%nat) | 49%nat => Z_to_bv 64 (V 49%nat) | 64%nat => Z_to_bv 64 (V 64%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 66%nat => Z_to_bv 64 (V 66%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | 69%nat => Z_to_bv 64 (V 69%nat) | 70%nat => Z_to_bv 64 (V 70%nat) | 71%nat => Z_to_bv 64 (V 71%nat) | 72%nat => Z_to_bv 64 (V 72%nat) | 73%nat => Z_to_bv 64 (V 73%nat) | 74%nat => Z_to_bv 64 (V 74%nat) | 75%nat => Z_to_bv 64 (V 75%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SRA (EVar 49) (ELit 48))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 69%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 70%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 71%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 74%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 75%nat)
        /\ L5.u8_at RSEGS M' (V 48%nat) 0
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450907) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450906) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450905) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450904) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450911) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450910) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450909) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450908) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450899) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450898) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450897) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450896) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450903) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450902) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450901) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450900) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450891) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450890) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450889) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450888) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450895) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450894) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450893) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450892) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450883) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450882) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450881) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450880) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450887) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450885) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 245
        /\ L5.u64_at RSEGS M' (V 47%nat) 1172321806
        /\ L5.defined M' ((V 47%nat) + 8) 248).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 pvzI19 K1 K2 pvzI20 K4 K5 K6 K7 K8 K9 pvzI21 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 pvzI22.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV48l; move HV48l before pvzI5; pose proof (proj2 pvzI5) as HV48r; move HV48r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV49l; move HV49l before pvzI6; pose proof (proj2 pvzI6) as HV49r; move HV49r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV64l; move HV64l before pvzI7; pose proof (proj2 pvzI7) as HV64r; move HV64r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV65l; move HV65l before pvzI8; pose proof (proj2 pvzI8) as HV65r; move HV65r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV66l; move HV66l before pvzI9; pose proof (proj2 pvzI9) as HV66r; move HV66r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV67l; move HV67l before pvzI10; pose proof (proj2 pvzI10) as HV67r; move HV67r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV68l; move HV68l before pvzI11; pose proof (proj2 pvzI11) as HV68r; move HV68r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV69l; move HV69l before pvzI12; pose proof (proj2 pvzI12) as HV69r; move HV69r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV70l; move HV70l before pvzI13; pose proof (proj2 pvzI13) as HV70r; move HV70r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV71l; move HV71l before pvzI14; pose proof (proj2 pvzI14) as HV71r; move HV71r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV72l; move HV72l before pvzI15; pose proof (proj2 pvzI15) as HV72r; move HV72r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV73l; move HV73l before pvzI16; pose proof (proj2 pvzI16) as HV73r; move HV73r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV74l; move HV74l before pvzI17; pose proof (proj2 pvzI17) as HV74r; move HV74r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV75l; move HV75l before pvzI18; pose proof (proj2 pvzI18) as HV75r; move HV75r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K0l; move K0l before pvzI19; pose proof (proj2 pvzI19) as K0r; move K0r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K3l; move K3l before pvzI20; pose proof (proj2 pvzI20) as K3r; move K3r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K10l; move K10l before pvzI21; pose proof (proj2 pvzI21) as K10r; move K10r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K28l; move K28l before pvzI22; pose proof (proj2 pvzI22) as K28r; move K28r before pvzI22; clear pvzI22.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *. set (vz_73 := V 73%nat) in *. set (vz_74 := V 74%nat) in *. set (vz_75 := V 75%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | 73%nat => Z_to_bv 64 vz_73 | 74%nat => Z_to_bv 64 vz_74 | 75%nat => Z_to_bv 64 vz_75 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | 73%nat => vz_73 | 74%nat => vz_74 | 75%nat => vz_75 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 76%nat. }
  assert (HR: regs_ok E PaglSIP.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaglSIP.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaglSIP.kn0).
  { unfold know_ok, PaglSIP.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K10l K10r K12 K13 K15; lia | clear - HV48l HV48r K10l K10r K12 K13 K15; lia | clear - HV48l HV48r K10l K10r K12 K13 K15; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV73l HV73r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV74l HV74r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV75l HV75r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV49l HV49r K28l K28r) | exact (conj K28l K28r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaglSIP.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaglSIP.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 32) -> ~ ((vz_48 + 0) <= bv_unsigned a < (vz_48 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PaglSIP.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K3l K3r K7 K13 K14 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K3l K3r K7 K13 K14 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | evalEk' ZA Hag ltac:(clear) | clear - HV48l HV48r K10l K10r K12 K13 K15 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaglSIP.ps0) with 0xb63c0 in Hms. change (SR.ps_regs PaglSIP.ps0) with (map (fun i => (i, nth i PaglSIP.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaglSIP.ps0) with PaglSIP.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaglSIP.regs0 PaglSIP.regs_out0 80 KS_aglSIP KS_aglSIP_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaglSIP.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaglSIP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSIP.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaglSIP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSIP.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaglSIP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSIP.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PaglSIP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSIP.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaglSIP.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
  split. { rewrite (BG.out_reg PaglSIP.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaglSIP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSIP.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaglSIP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSIP.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaglSIP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSIP.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PaglSIP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSIP.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PaglSIP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSIP.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PaglSIP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSIP.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PaglSIP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSIP.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PaglSIP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSIP.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PaglSIP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSIP.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PaglSIP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 23%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 24%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 25%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 26%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 27%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 28%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 29%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 30%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 31%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 32%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 33%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 34%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PaglSlP := BndP_Ea_024S8.LibSegEa_aglSlP.
Definition KS_aglSlP : list nat := Eval vm_compute in (BG.kept_list 80 PaglSlP.regs0 PaglSlP.regs_out0).
Lemma KS_aglSlP_ok : BG.kept_ok 80 PaglSlP.regs0 PaglSlP.regs_out0 KS_aglSlP = true. Proof. vm_compute. reflexivity. Qed.
Lemma aglSlP_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 49%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 22) = Z_to_bv 64 4 -> getr R (reg 23) = Z_to_bv 64 ((V 47%nat) + 96) -> getr R (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6914048 <= (V 47%nat) <= 140737488355072 ->
  aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 256 -> L5.writable RSEGS M (V 47%nat) 256 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 256 <= 2147446784) ->
  L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 32 -> L5.u64_at RSEGS M ((V 47%nat) + 248) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 256 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 256 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 64%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 67%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 68%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 71%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 72) (V 72%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 73%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 74%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 75%nat) ->
  0 <= (V 49%nat) <= 9223372036854775807 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 32) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 32) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb6224 M) (st fx' R' 0xb63c0 M')
        /\ (forall x, In x KS_aglSlP -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 69%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 70%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 71%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 74%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 75%nat)
        /\ L5.u8_at RSEGS M' (V 48%nat) 0
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450907) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450906) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450905) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450904) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450911) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450910) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450909) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450908) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450899) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450898) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450897) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450896) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450903) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450902) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450901) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450900) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450891) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450890) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450889) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450888) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450895) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450894) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450893) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450892) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450883) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450882) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450881) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450880) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450887) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450885) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 245
        /\ L5.u64_at RSEGS M' (V 47%nat) 1172321806
        /\ L5.defined M' ((V 47%nat) + 8) 248).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 pvzI19 K1 K2 pvzI20 K4 K5 K6 K7 K8 K9 pvzI21 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 pvzI22.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV48l; move HV48l before pvzI5; pose proof (proj2 pvzI5) as HV48r; move HV48r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV49l; move HV49l before pvzI6; pose proof (proj2 pvzI6) as HV49r; move HV49r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV64l; move HV64l before pvzI7; pose proof (proj2 pvzI7) as HV64r; move HV64r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV65l; move HV65l before pvzI8; pose proof (proj2 pvzI8) as HV65r; move HV65r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV66l; move HV66l before pvzI9; pose proof (proj2 pvzI9) as HV66r; move HV66r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV67l; move HV67l before pvzI10; pose proof (proj2 pvzI10) as HV67r; move HV67r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV68l; move HV68l before pvzI11; pose proof (proj2 pvzI11) as HV68r; move HV68r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV69l; move HV69l before pvzI12; pose proof (proj2 pvzI12) as HV69r; move HV69r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV70l; move HV70l before pvzI13; pose proof (proj2 pvzI13) as HV70r; move HV70r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV71l; move HV71l before pvzI14; pose proof (proj2 pvzI14) as HV71r; move HV71r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV72l; move HV72l before pvzI15; pose proof (proj2 pvzI15) as HV72r; move HV72r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV73l; move HV73l before pvzI16; pose proof (proj2 pvzI16) as HV73r; move HV73r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV74l; move HV74l before pvzI17; pose proof (proj2 pvzI17) as HV74r; move HV74r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV75l; move HV75l before pvzI18; pose proof (proj2 pvzI18) as HV75r; move HV75r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K0l; move K0l before pvzI19; pose proof (proj2 pvzI19) as K0r; move K0r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K3l; move K3l before pvzI20; pose proof (proj2 pvzI20) as K3r; move K3r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K10l; move K10l before pvzI21; pose proof (proj2 pvzI21) as K10r; move K10r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K28l; move K28l before pvzI22; pose proof (proj2 pvzI22) as K28r; move K28r before pvzI22; clear pvzI22.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *. set (vz_73 := V 73%nat) in *. set (vz_74 := V 74%nat) in *. set (vz_75 := V 75%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | 73%nat => Z_to_bv 64 vz_73 | 74%nat => Z_to_bv 64 vz_74 | 75%nat => Z_to_bv 64 vz_75 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | 73%nat => vz_73 | 74%nat => vz_74 | 75%nat => vz_75 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 76%nat. }
  assert (HR: regs_ok E PaglSlP.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaglSlP.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaglSlP.kn0).
  { unfold know_ok, PaglSlP.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K10l K10r K12 K13 K15; lia | clear - HV48l HV48r K10l K10r K12 K13 K15; lia | clear - HV48l HV48r K10l K10r K12 K13 K15; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV73l HV73r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV74l HV74r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV75l HV75r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV49l HV49r K28l K28r) | exact (conj K28l K28r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaglSlP.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaglSlP.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 32) -> ~ ((vz_48 + 0) <= bv_unsigned a < (vz_48 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PaglSlP.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K3l K3r K7 K13 K14 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K3l K3r K7 K13 K14 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | evalEk' ZA Hag ltac:(clear) | clear - HV48l HV48r K10l K10r K12 K13 K15 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaglSlP.ps0) with 0xb63c0 in Hms. change (SR.ps_regs PaglSlP.ps0) with (map (fun i => (i, nth i PaglSlP.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaglSlP.ps0) with PaglSlP.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaglSlP.regs0 PaglSlP.regs_out0 80 KS_aglSlP KS_aglSlP_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaglSlP.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaglSlP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSlP.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaglSlP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSlP.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaglSlP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSlP.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PaglSlP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSlP.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaglSlP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSlP.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaglSlP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSlP.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaglSlP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSlP.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PaglSlP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSlP.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PaglSlP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSlP.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PaglSlP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSlP.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PaglSlP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSlP.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PaglSlP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSlP.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PaglSlP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSlP.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PaglSlP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 23%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 24%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 25%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 26%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 27%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 28%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 29%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 30%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 31%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 32%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 33%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 34%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PaglSLP := BndP_Ea_023S8.LibSegEa_aglSLP.
Definition KS_aglSLP : list nat := Eval vm_compute in (BG.kept_list 80 PaglSLP.regs0 PaglSLP.regs_out0).
Lemma KS_aglSLP_ok : BG.kept_ok 80 PaglSLP.regs0 PaglSLP.regs_out0 KS_aglSLP = true. Proof. vm_compute. reflexivity. Qed.
Lemma aglSLP_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 49%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 22) = Z_to_bv 64 ((V 47%nat) + 112) -> getr R (reg 23) = Z_to_bv 64 8 -> getr R (reg 24) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6914048 <= (V 47%nat) <= 140737488355072 ->
  aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 256 -> L5.writable RSEGS M (V 47%nat) 256 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 256 <= 2147446784) ->
  L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 32 -> L5.u64_at RSEGS M ((V 47%nat) + 248) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 256 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 256 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 64%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 67%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 68%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 71%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 72) (V 72%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 73%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 74%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 75%nat) ->
  0 <= (V 49%nat) <= 9223372036854775807 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 32) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 32) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb61a0 M) (st fx' R' 0xb63c0 M')
        /\ (forall x, In x KS_aglSLP -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 69%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 70%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 71%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 74%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 75%nat)
        /\ L5.u8_at RSEGS M' (V 48%nat) 0
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450907) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450906) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450905) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450904) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450911) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450910) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450909) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450908) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450899) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450898) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450897) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450896) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450903) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450902) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450901) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450900) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450891) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450890) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450889) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450888) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450895) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450894) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450893) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450892) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450883) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450882) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450881) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450880) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450887) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450885) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 245
        /\ L5.u64_at RSEGS M' (V 47%nat) 1172321806
        /\ L5.defined M' ((V 47%nat) + 8) 248).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 pvzI19 K1 K2 pvzI20 K4 K5 K6 K7 K8 K9 pvzI21 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 pvzI22.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV48l; move HV48l before pvzI5; pose proof (proj2 pvzI5) as HV48r; move HV48r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV49l; move HV49l before pvzI6; pose proof (proj2 pvzI6) as HV49r; move HV49r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV64l; move HV64l before pvzI7; pose proof (proj2 pvzI7) as HV64r; move HV64r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV65l; move HV65l before pvzI8; pose proof (proj2 pvzI8) as HV65r; move HV65r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV66l; move HV66l before pvzI9; pose proof (proj2 pvzI9) as HV66r; move HV66r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV67l; move HV67l before pvzI10; pose proof (proj2 pvzI10) as HV67r; move HV67r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV68l; move HV68l before pvzI11; pose proof (proj2 pvzI11) as HV68r; move HV68r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV69l; move HV69l before pvzI12; pose proof (proj2 pvzI12) as HV69r; move HV69r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV70l; move HV70l before pvzI13; pose proof (proj2 pvzI13) as HV70r; move HV70r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV71l; move HV71l before pvzI14; pose proof (proj2 pvzI14) as HV71r; move HV71r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV72l; move HV72l before pvzI15; pose proof (proj2 pvzI15) as HV72r; move HV72r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV73l; move HV73l before pvzI16; pose proof (proj2 pvzI16) as HV73r; move HV73r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV74l; move HV74l before pvzI17; pose proof (proj2 pvzI17) as HV74r; move HV74r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV75l; move HV75l before pvzI18; pose proof (proj2 pvzI18) as HV75r; move HV75r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K0l; move K0l before pvzI19; pose proof (proj2 pvzI19) as K0r; move K0r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K3l; move K3l before pvzI20; pose proof (proj2 pvzI20) as K3r; move K3r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K10l; move K10l before pvzI21; pose proof (proj2 pvzI21) as K10r; move K10r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K28l; move K28l before pvzI22; pose proof (proj2 pvzI22) as K28r; move K28r before pvzI22; clear pvzI22.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *. set (vz_73 := V 73%nat) in *. set (vz_74 := V 74%nat) in *. set (vz_75 := V 75%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | 73%nat => Z_to_bv 64 vz_73 | 74%nat => Z_to_bv 64 vz_74 | 75%nat => Z_to_bv 64 vz_75 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | 73%nat => vz_73 | 74%nat => vz_74 | 75%nat => vz_75 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 76%nat. }
  assert (HR: regs_ok E PaglSLP.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaglSLP.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaglSLP.kn0).
  { unfold know_ok, PaglSLP.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | clear - HV47l HV47r K3l K3r K7 K13 K14; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K10l K10r K12 K13 K15; lia | clear - HV48l HV48r K10l K10r K12 K13 K15; lia | clear - HV48l HV48r K10l K10r K12 K13 K15; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV73l HV73r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV74l HV74r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV75l HV75r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV49l HV49r K28l K28r) | exact (conj K28l K28r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaglSLP.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaglSLP.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 32) -> ~ ((vz_48 + 0) <= bv_unsigned a < (vz_48 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PaglSLP.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K3l K3r K7 K13 K14 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K3l K3r K7 K13 K14 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | evalEk' ZA Hag ltac:(clear) | clear - HV48l HV48r K10l K10r K12 K13 K15 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaglSLP.ps0) with 0xb63c0 in Hms. change (SR.ps_regs PaglSLP.ps0) with (map (fun i => (i, nth i PaglSLP.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaglSLP.ps0) with PaglSLP.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaglSLP.regs0 PaglSLP.regs_out0 80 KS_aglSLP KS_aglSLP_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaglSLP.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaglSLP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSLP.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaglSLP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSLP.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaglSLP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSLP.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PaglSLP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSLP.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaglSLP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSLP.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaglSLP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSLP.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaglSLP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSLP.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PaglSLP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSLP.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PaglSLP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSLP.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PaglSLP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSLP.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PaglSLP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSLP.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PaglSLP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSLP.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PaglSLP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaglSLP.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PaglSLP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV48l HV48r K10l K10r K12 K13 K15) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 23%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 24%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 25%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 26%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 27%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 28%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 29%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 30%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 31%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 32%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 33%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 34%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

End PEAGLWP.
