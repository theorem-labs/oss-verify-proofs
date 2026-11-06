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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.seg Require BndP_Ea_062S8 BndP_Ea_063S8 BndP_Ea_064S8.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PECVALARP3.
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

Module PavrF5Z := BndP_Ea_062S8.LibSegEa_avrF5Z.
Definition KS_avrF5Z_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF5Z.regs0 PavrF5Z.regs_out0).
Lemma KS_avrF5Z_0_ok : BG.kept_ok 60 PavrF5Z.regs0 PavrF5Z.regs_out0 KS_avrF5Z_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avrF5Z_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF5Z.regs0 PavrF5Z.regs_out1).
Lemma KS_avrF5Z_1_ok : BG.kept_ok 60 PavrF5Z.regs0 PavrF5Z.regs_out1 KS_avrF5Z_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrF5Z_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 5) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5KA.zeros_at M ((((V 33%nat) + 5) / 8) + 2147450880) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb5c7c M) (st fx' R' 0xb5cdc M')
        /\ (forall x, In x KS_avrF5Z_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb5c7c M) (st fx' R' 0xb5c98 M')
        /\ (forall x, In x KS_avrF5Z_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ getr R' (reg 11) = Z_to_bv 64 0
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
  assert (HR: regs_ok E PavrF5Z.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrF5Z.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrF5Z.kn0).
  { unfold know_ok, PavrF5Z.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrF5Z.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrF5Z.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavrF5Z.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavrF5Z.ps0) with 0xb5cdc in Hms. change (SR.ps_regs PavrF5Z.ps0) with (map (fun i => (i, nth i PavrF5Z.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF5Z.ps0) with PavrF5Z.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF5Z.regs0 PavrF5Z.regs_out0 60 KS_avrF5Z_0 KS_avrF5Z_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF5Z.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF5Z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF5Z.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF5Z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF5Z.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF5Z.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  - right.
    change (SR.ps_pc PavrF5Z.ps1) with 0xb5c98 in Hms. change (SR.ps_regs PavrF5Z.ps1) with (map (fun i => (i, nth i PavrF5Z.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF5Z.ps1) with PavrF5Z.cells1 in Hcells. unfold PavrF5Z.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF5Z.regs0 PavrF5Z.regs_out1 60 KS_avrF5Z_1 KS_avrF5Z_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF5Z.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF5Z.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF5Z.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF5Z.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF5Z.regs_out1 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF5Z.regs_out1]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
Qed.

Module PavrF5P1 := BndP_Ea_062S8.LibSegEa_avrF5P1.
Definition KS_avrF5P1_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF5P1.regs0 PavrF5P1.regs_out0).
Lemma KS_avrF5P1_0_ok : BG.kept_ok 60 PavrF5P1.regs0 PavrF5P1.regs_out0 KS_avrF5P1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avrF5P1_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF5P1.regs0 PavrF5P1.regs_out1).
Lemma KS_avrF5P1_1_ok : BG.kept_ok 60 PavrF5P1.regs0 PavrF5P1.regs_out1 KS_avrF5P1_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrF5P1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 5) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 5) / 8) + 2147450880) 1 -> 0 <= (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7) <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb5c7c M) (st fx' R' 0xb5cdc M')
        /\ (forall x, In x KS_avrF5P1_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb5c7c M) (st fx' R' 0xb5c98 M')
        /\ (forall x, In x KS_avrF5P1_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G12 G14 G15 G16 G17 G18 G19 G20 G21 G22 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavrF5P1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrF5P1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrF5P1.kn0).
  { unfold know_ok, PavrF5P1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrF5P1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrF5P1.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavrF5P1.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavrF5P1.ps0) with 0xb5cdc in Hms. change (SR.ps_regs PavrF5P1.ps0) with (map (fun i => (i, nth i PavrF5P1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF5P1.ps0) with PavrF5P1.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF5P1.regs0 PavrF5P1.regs_out0 60 KS_avrF5P1_0 KS_avrF5P1_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF5P1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF5P1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF5P1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF5P1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF5P1.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrF5P1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF5P1.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF5P1.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  - right.
    change (SR.ps_pc PavrF5P1.ps1) with 0xb5c98 in Hms. change (SR.ps_regs PavrF5P1.ps1) with (map (fun i => (i, nth i PavrF5P1.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF5P1.ps1) with PavrF5P1.cells1 in Hcells. unfold PavrF5P1.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF5P1.regs0 PavrF5P1.regs_out1 60 KS_avrF5P1_1 KS_avrF5P1_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF5P1.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF5P1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF5P1.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF5P1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF5P1.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrF5P1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF5P1.regs_out1 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF5P1.regs_out1]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
Qed.

Module PavrF5P2 := BndP_Ea_062S8.LibSegEa_avrF5P2.
Definition KS_avrF5P2_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF5P2.regs0 PavrF5P2.regs_out0).
Lemma KS_avrF5P2_0_ok : BG.kept_ok 60 PavrF5P2.regs0 PavrF5P2.regs_out0 KS_avrF5P2_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avrF5P2_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF5P2.regs0 PavrF5P2.regs_out1).
Lemma KS_avrF5P2_1_ok : BG.kept_ok 60 PavrF5P2.regs0 PavrF5P2.regs_out1 KS_avrF5P2_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrF5P2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 5) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 5) / 8) + 2147450880) 2 -> 0 <= (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb5c7c M) (st fx' R' 0xb5cdc M')
        /\ (forall x, In x KS_avrF5P2_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb5c7c M) (st fx' R' 0xb5c98 M')
        /\ (forall x, In x KS_avrF5P2_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G12 G14 G15 G16 G17 G18 G19 G20 G21 G22 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavrF5P2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrF5P2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrF5P2.kn0).
  { unfold know_ok, PavrF5P2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrF5P2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrF5P2.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavrF5P2.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavrF5P2.ps0) with 0xb5cdc in Hms. change (SR.ps_regs PavrF5P2.ps0) with (map (fun i => (i, nth i PavrF5P2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF5P2.ps0) with PavrF5P2.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF5P2.regs0 PavrF5P2.regs_out0 60 KS_avrF5P2_0 KS_avrF5P2_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF5P2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF5P2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF5P2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF5P2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF5P2.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrF5P2.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PavrF5P2.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF5P2.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  - right.
    change (SR.ps_pc PavrF5P2.ps1) with 0xb5c98 in Hms. change (SR.ps_regs PavrF5P2.ps1) with (map (fun i => (i, nth i PavrF5P2.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF5P2.ps1) with PavrF5P2.cells1 in Hcells. unfold PavrF5P2.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF5P2.regs0 PavrF5P2.regs_out1 60 KS_avrF5P2_1 KS_avrF5P2_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF5P2.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF5P2.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF5P2.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF5P2.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF5P2.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrF5P2.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PavrF5P2.regs_out1 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF5P2.regs_out1]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
Qed.

Module PavrF5P3 := BndP_Ea_062S8.LibSegEa_avrF5P3.
Definition KS_avrF5P3_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF5P3.regs0 PavrF5P3.regs_out0).
Lemma KS_avrF5P3_0_ok : BG.kept_ok 60 PavrF5P3.regs0 PavrF5P3.regs_out0 KS_avrF5P3_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avrF5P3_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF5P3.regs0 PavrF5P3.regs_out1).
Lemma KS_avrF5P3_1_ok : BG.kept_ok 60 PavrF5P3.regs0 PavrF5P3.regs_out1 KS_avrF5P3_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrF5P3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 5) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 5) / 8) + 2147450880) 3 -> 0 <= (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7) <= 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb5c7c M) (st fx' R' 0xb5cdc M')
        /\ (forall x, In x KS_avrF5P3_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ getr R' (reg 11) = Z_to_bv 64 3
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb5c7c M) (st fx' R' 0xb5c98 M')
        /\ (forall x, In x KS_avrF5P3_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ getr R' (reg 11) = Z_to_bv 64 3
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G12 G14 G15 G16 G17 G18 G19 G20 G21 G22 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavrF5P3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrF5P3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrF5P3.kn0).
  { unfold know_ok, PavrF5P3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrF5P3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrF5P3.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavrF5P3.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavrF5P3.ps0) with 0xb5cdc in Hms. change (SR.ps_regs PavrF5P3.ps0) with (map (fun i => (i, nth i PavrF5P3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF5P3.ps0) with PavrF5P3.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF5P3.regs0 PavrF5P3.regs_out0 60 KS_avrF5P3_0 KS_avrF5P3_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF5P3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF5P3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF5P3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF5P3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF5P3.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrF5P3.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PavrF5P3.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF5P3.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  - right.
    change (SR.ps_pc PavrF5P3.ps1) with 0xb5c98 in Hms. change (SR.ps_regs PavrF5P3.ps1) with (map (fun i => (i, nth i PavrF5P3.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF5P3.ps1) with PavrF5P3.cells1 in Hcells. unfold PavrF5P3.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF5P3.regs0 PavrF5P3.regs_out1 60 KS_avrF5P3_1 KS_avrF5P3_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF5P3.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF5P3.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF5P3.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF5P3.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF5P3.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrF5P3.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PavrF5P3.regs_out1 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF5P3.regs_out1]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
Qed.

Module PavrF5P4 := BndP_Ea_062S8.LibSegEa_avrF5P4.
Definition KS_avrF5P4_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF5P4.regs0 PavrF5P4.regs_out0).
Lemma KS_avrF5P4_0_ok : BG.kept_ok 60 PavrF5P4.regs0 PavrF5P4.regs_out0 KS_avrF5P4_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avrF5P4_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF5P4.regs0 PavrF5P4.regs_out1).
Lemma KS_avrF5P4_1_ok : BG.kept_ok 60 PavrF5P4.regs0 PavrF5P4.regs_out1 KS_avrF5P4_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrF5P4_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 5) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 5) / 8) + 2147450880) 4 -> 0 <= (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7) <= 3 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb5c7c M) (st fx' R' 0xb5cdc M')
        /\ (forall x, In x KS_avrF5P4_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ getr R' (reg 11) = Z_to_bv 64 4
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb5c7c M) (st fx' R' 0xb5c98 M')
        /\ (forall x, In x KS_avrF5P4_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ getr R' (reg 11) = Z_to_bv 64 4
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G12 G14 G15 G16 G17 G18 G19 G20 G21 G22 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavrF5P4.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrF5P4.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrF5P4.kn0).
  { unfold know_ok, PavrF5P4.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrF5P4.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrF5P4.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavrF5P4.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavrF5P4.ps0) with 0xb5cdc in Hms. change (SR.ps_regs PavrF5P4.ps0) with (map (fun i => (i, nth i PavrF5P4.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF5P4.ps0) with PavrF5P4.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF5P4.regs0 PavrF5P4.regs_out0 60 KS_avrF5P4_0 KS_avrF5P4_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF5P4.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF5P4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF5P4.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF5P4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF5P4.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrF5P4.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PavrF5P4.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF5P4.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  - right.
    change (SR.ps_pc PavrF5P4.ps1) with 0xb5c98 in Hms. change (SR.ps_regs PavrF5P4.ps1) with (map (fun i => (i, nth i PavrF5P4.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF5P4.ps1) with PavrF5P4.cells1 in Hcells. unfold PavrF5P4.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF5P4.regs0 PavrF5P4.regs_out1 60 KS_avrF5P4_1 KS_avrF5P4_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF5P4.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF5P4.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF5P4.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF5P4.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF5P4.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrF5P4.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PavrF5P4.regs_out1 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF5P4.regs_out1]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
Qed.

Module PavrF5P5 := BndP_Ea_062S8.LibSegEa_avrF5P5.
Definition KS_avrF5P5_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF5P5.regs0 PavrF5P5.regs_out0).
Lemma KS_avrF5P5_0_ok : BG.kept_ok 60 PavrF5P5.regs0 PavrF5P5.regs_out0 KS_avrF5P5_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avrF5P5_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF5P5.regs0 PavrF5P5.regs_out1).
Lemma KS_avrF5P5_1_ok : BG.kept_ok 60 PavrF5P5.regs0 PavrF5P5.regs_out1 KS_avrF5P5_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrF5P5_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 5) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 5) / 8) + 2147450880) 5 -> 0 <= (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7) <= 4 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb5c7c M) (st fx' R' 0xb5cdc M')
        /\ (forall x, In x KS_avrF5P5_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ getr R' (reg 11) = Z_to_bv 64 5
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb5c7c M) (st fx' R' 0xb5c98 M')
        /\ (forall x, In x KS_avrF5P5_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ getr R' (reg 11) = Z_to_bv 64 5
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G12 G14 G15 G16 G17 G18 G19 G20 G21 G22 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavrF5P5.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrF5P5.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrF5P5.kn0).
  { unfold know_ok, PavrF5P5.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrF5P5.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrF5P5.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavrF5P5.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavrF5P5.ps0) with 0xb5cdc in Hms. change (SR.ps_regs PavrF5P5.ps0) with (map (fun i => (i, nth i PavrF5P5.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF5P5.ps0) with PavrF5P5.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF5P5.regs0 PavrF5P5.regs_out0 60 KS_avrF5P5_0 KS_avrF5P5_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF5P5.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF5P5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF5P5.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF5P5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF5P5.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrF5P5.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PavrF5P5.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF5P5.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  - right.
    change (SR.ps_pc PavrF5P5.ps1) with 0xb5c98 in Hms. change (SR.ps_regs PavrF5P5.ps1) with (map (fun i => (i, nth i PavrF5P5.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF5P5.ps1) with PavrF5P5.cells1 in Hcells. unfold PavrF5P5.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF5P5.regs0 PavrF5P5.regs_out1 60 KS_avrF5P5_1 KS_avrF5P5_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF5P5.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF5P5.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF5P5.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF5P5.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF5P5.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrF5P5.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PavrF5P5.regs_out1 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF5P5.regs_out1]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
Qed.

Module PavrF5P6 := BndP_Ea_062S8.LibSegEa_avrF5P6.
Definition KS_avrF5P6_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF5P6.regs0 PavrF5P6.regs_out0).
Lemma KS_avrF5P6_0_ok : BG.kept_ok 60 PavrF5P6.regs0 PavrF5P6.regs_out0 KS_avrF5P6_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avrF5P6_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF5P6.regs0 PavrF5P6.regs_out1).
Lemma KS_avrF5P6_1_ok : BG.kept_ok 60 PavrF5P6.regs0 PavrF5P6.regs_out1 KS_avrF5P6_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrF5P6_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 5) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 5) / 8) + 2147450880) 6 -> 0 <= (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7) <= 5 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb5c7c M) (st fx' R' 0xb5cdc M')
        /\ (forall x, In x KS_avrF5P6_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb5c7c M) (st fx' R' 0xb5c98 M')
        /\ (forall x, In x KS_avrF5P6_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G12 G14 G15 G16 G17 G18 G19 G20 G21 G22 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavrF5P6.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrF5P6.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrF5P6.kn0).
  { unfold know_ok, PavrF5P6.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrF5P6.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrF5P6.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavrF5P6.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavrF5P6.ps0) with 0xb5cdc in Hms. change (SR.ps_regs PavrF5P6.ps0) with (map (fun i => (i, nth i PavrF5P6.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF5P6.ps0) with PavrF5P6.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF5P6.regs0 PavrF5P6.regs_out0 60 KS_avrF5P6_0 KS_avrF5P6_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF5P6.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF5P6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF5P6.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF5P6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF5P6.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrF5P6.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PavrF5P6.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF5P6.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  - right.
    change (SR.ps_pc PavrF5P6.ps1) with 0xb5c98 in Hms. change (SR.ps_regs PavrF5P6.ps1) with (map (fun i => (i, nth i PavrF5P6.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF5P6.ps1) with PavrF5P6.cells1 in Hcells. unfold PavrF5P6.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF5P6.regs0 PavrF5P6.regs_out1 60 KS_avrF5P6_1 KS_avrF5P6_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF5P6.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF5P6.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF5P6.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF5P6.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF5P6.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrF5P6.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PavrF5P6.regs_out1 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF5P6.regs_out1]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
Qed.

Module PavrF5P7 := BndP_Ea_062S8.LibSegEa_avrF5P7.
Definition KS_avrF5P7_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF5P7.regs0 PavrF5P7.regs_out0).
Lemma KS_avrF5P7_0_ok : BG.kept_ok 60 PavrF5P7.regs0 PavrF5P7.regs_out0 KS_avrF5P7_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avrF5P7_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF5P7.regs0 PavrF5P7.regs_out1).
Lemma KS_avrF5P7_1_ok : BG.kept_ok 60 PavrF5P7.regs0 PavrF5P7.regs_out1 KS_avrF5P7_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrF5P7_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 5) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 5) / 8) + 2147450880) 7 -> 0 <= (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7) <= 6 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb5c7c M) (st fx' R' 0xb5cdc M')
        /\ (forall x, In x KS_avrF5P7_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ getr R' (reg 11) = Z_to_bv 64 7
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb5c7c M) (st fx' R' 0xb5c98 M')
        /\ (forall x, In x KS_avrF5P7_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ getr R' (reg 11) = Z_to_bv 64 7
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G12 G14 G15 G16 G17 G18 G19 G20 G21 G22 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavrF5P7.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrF5P7.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrF5P7.kn0).
  { unfold know_ok, PavrF5P7.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrF5P7.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrF5P7.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavrF5P7.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavrF5P7.ps0) with 0xb5cdc in Hms. change (SR.ps_regs PavrF5P7.ps0) with (map (fun i => (i, nth i PavrF5P7.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF5P7.ps0) with PavrF5P7.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF5P7.regs0 PavrF5P7.regs_out0 60 KS_avrF5P7_0 KS_avrF5P7_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF5P7.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF5P7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF5P7.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF5P7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF5P7.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrF5P7.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PavrF5P7.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF5P7.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  - right.
    change (SR.ps_pc PavrF5P7.ps1) with 0xb5c98 in Hms. change (SR.ps_regs PavrF5P7.ps1) with (map (fun i => (i, nth i PavrF5P7.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF5P7.ps1) with PavrF5P7.cells1 in Hcells. unfold PavrF5P7.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF5P7.regs0 PavrF5P7.regs_out1 60 KS_avrF5P7_1 KS_avrF5P7_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF5P7.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF5P7.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF5P7.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF5P7.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF5P7.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrF5P7.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PavrF5P7.regs_out1 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF5P7.regs_out1]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
Qed.

Module PavrF6Z := BndP_Ea_063S8.LibSegEa_avrF6Z.
Definition KS_avrF6Z_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF6Z.regs0 PavrF6Z.regs_out0).
Lemma KS_avrF6Z_0_ok : BG.kept_ok 60 PavrF6Z.regs0 PavrF6Z.regs_out0 KS_avrF6Z_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avrF6Z_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF6Z.regs0 PavrF6Z.regs_out1).
Lemma KS_avrF6Z_1_ok : BG.kept_ok 60 PavrF6Z.regs0 PavrF6Z.regs_out1 KS_avrF6Z_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrF6Z_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 6) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5KA.zeros_at M ((((V 33%nat) + 6) / 8) + 2147450880) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb5c98 M) (st fx' R' 0xb5cdc M')
        /\ (forall x, In x KS_avrF6Z_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb5c98 M) (st fx' R' 0xb5cb4 M')
        /\ (forall x, In x KS_avrF6Z_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ getr R' (reg 11) = Z_to_bv 64 0
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
  assert (HR: regs_ok E PavrF6Z.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrF6Z.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrF6Z.kn0).
  { unfold know_ok, PavrF6Z.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrF6Z.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrF6Z.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavrF6Z.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavrF6Z.ps0) with 0xb5cdc in Hms. change (SR.ps_regs PavrF6Z.ps0) with (map (fun i => (i, nth i PavrF6Z.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF6Z.ps0) with PavrF6Z.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF6Z.regs0 PavrF6Z.regs_out0 60 KS_avrF6Z_0 KS_avrF6Z_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF6Z.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF6Z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF6Z.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF6Z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF6Z.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF6Z.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  - right.
    change (SR.ps_pc PavrF6Z.ps1) with 0xb5cb4 in Hms. change (SR.ps_regs PavrF6Z.ps1) with (map (fun i => (i, nth i PavrF6Z.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF6Z.ps1) with PavrF6Z.cells1 in Hcells. unfold PavrF6Z.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF6Z.regs0 PavrF6Z.regs_out1 60 KS_avrF6Z_1 KS_avrF6Z_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF6Z.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF6Z.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF6Z.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF6Z.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF6Z.regs_out1 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF6Z.regs_out1]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
Qed.

Module PavrF6P1 := BndP_Ea_063S8.LibSegEa_avrF6P1.
Definition KS_avrF6P1_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF6P1.regs0 PavrF6P1.regs_out0).
Lemma KS_avrF6P1_0_ok : BG.kept_ok 60 PavrF6P1.regs0 PavrF6P1.regs_out0 KS_avrF6P1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avrF6P1_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF6P1.regs0 PavrF6P1.regs_out1).
Lemma KS_avrF6P1_1_ok : BG.kept_ok 60 PavrF6P1.regs0 PavrF6P1.regs_out1 KS_avrF6P1_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrF6P1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 6) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 6) / 8) + 2147450880) 1 -> 0 <= (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7) <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb5c98 M) (st fx' R' 0xb5cdc M')
        /\ (forall x, In x KS_avrF6P1_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb5c98 M) (st fx' R' 0xb5cb4 M')
        /\ (forall x, In x KS_avrF6P1_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G12 G14 G15 G16 G17 G18 G19 G20 G21 G22 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavrF6P1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrF6P1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrF6P1.kn0).
  { unfold know_ok, PavrF6P1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrF6P1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrF6P1.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavrF6P1.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavrF6P1.ps0) with 0xb5cdc in Hms. change (SR.ps_regs PavrF6P1.ps0) with (map (fun i => (i, nth i PavrF6P1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF6P1.ps0) with PavrF6P1.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF6P1.regs0 PavrF6P1.regs_out0 60 KS_avrF6P1_0 KS_avrF6P1_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF6P1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF6P1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF6P1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF6P1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF6P1.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrF6P1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF6P1.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF6P1.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  - right.
    change (SR.ps_pc PavrF6P1.ps1) with 0xb5cb4 in Hms. change (SR.ps_regs PavrF6P1.ps1) with (map (fun i => (i, nth i PavrF6P1.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF6P1.ps1) with PavrF6P1.cells1 in Hcells. unfold PavrF6P1.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF6P1.regs0 PavrF6P1.regs_out1 60 KS_avrF6P1_1 KS_avrF6P1_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF6P1.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF6P1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF6P1.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF6P1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF6P1.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrF6P1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF6P1.regs_out1 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF6P1.regs_out1]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
Qed.

Module PavrF6P2 := BndP_Ea_063S8.LibSegEa_avrF6P2.
Definition KS_avrF6P2_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF6P2.regs0 PavrF6P2.regs_out0).
Lemma KS_avrF6P2_0_ok : BG.kept_ok 60 PavrF6P2.regs0 PavrF6P2.regs_out0 KS_avrF6P2_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avrF6P2_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF6P2.regs0 PavrF6P2.regs_out1).
Lemma KS_avrF6P2_1_ok : BG.kept_ok 60 PavrF6P2.regs0 PavrF6P2.regs_out1 KS_avrF6P2_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrF6P2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 6) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 6) / 8) + 2147450880) 2 -> 0 <= (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb5c98 M) (st fx' R' 0xb5cdc M')
        /\ (forall x, In x KS_avrF6P2_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb5c98 M) (st fx' R' 0xb5cb4 M')
        /\ (forall x, In x KS_avrF6P2_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G12 G14 G15 G16 G17 G18 G19 G20 G21 G22 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavrF6P2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrF6P2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrF6P2.kn0).
  { unfold know_ok, PavrF6P2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrF6P2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrF6P2.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavrF6P2.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavrF6P2.ps0) with 0xb5cdc in Hms. change (SR.ps_regs PavrF6P2.ps0) with (map (fun i => (i, nth i PavrF6P2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF6P2.ps0) with PavrF6P2.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF6P2.regs0 PavrF6P2.regs_out0 60 KS_avrF6P2_0 KS_avrF6P2_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF6P2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF6P2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF6P2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF6P2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF6P2.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrF6P2.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PavrF6P2.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF6P2.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  - right.
    change (SR.ps_pc PavrF6P2.ps1) with 0xb5cb4 in Hms. change (SR.ps_regs PavrF6P2.ps1) with (map (fun i => (i, nth i PavrF6P2.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF6P2.ps1) with PavrF6P2.cells1 in Hcells. unfold PavrF6P2.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF6P2.regs0 PavrF6P2.regs_out1 60 KS_avrF6P2_1 KS_avrF6P2_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF6P2.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF6P2.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF6P2.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF6P2.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF6P2.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrF6P2.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PavrF6P2.regs_out1 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF6P2.regs_out1]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
Qed.

Module PavrF6P3 := BndP_Ea_063S8.LibSegEa_avrF6P3.
Definition KS_avrF6P3_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF6P3.regs0 PavrF6P3.regs_out0).
Lemma KS_avrF6P3_0_ok : BG.kept_ok 60 PavrF6P3.regs0 PavrF6P3.regs_out0 KS_avrF6P3_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avrF6P3_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF6P3.regs0 PavrF6P3.regs_out1).
Lemma KS_avrF6P3_1_ok : BG.kept_ok 60 PavrF6P3.regs0 PavrF6P3.regs_out1 KS_avrF6P3_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrF6P3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 6) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 6) / 8) + 2147450880) 3 -> 0 <= (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7) <= 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb5c98 M) (st fx' R' 0xb5cdc M')
        /\ (forall x, In x KS_avrF6P3_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ getr R' (reg 11) = Z_to_bv 64 3
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb5c98 M) (st fx' R' 0xb5cb4 M')
        /\ (forall x, In x KS_avrF6P3_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ getr R' (reg 11) = Z_to_bv 64 3
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G12 G14 G15 G16 G17 G18 G19 G20 G21 G22 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavrF6P3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrF6P3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrF6P3.kn0).
  { unfold know_ok, PavrF6P3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrF6P3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrF6P3.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavrF6P3.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavrF6P3.ps0) with 0xb5cdc in Hms. change (SR.ps_regs PavrF6P3.ps0) with (map (fun i => (i, nth i PavrF6P3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF6P3.ps0) with PavrF6P3.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF6P3.regs0 PavrF6P3.regs_out0 60 KS_avrF6P3_0 KS_avrF6P3_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF6P3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF6P3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF6P3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF6P3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF6P3.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrF6P3.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PavrF6P3.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF6P3.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  - right.
    change (SR.ps_pc PavrF6P3.ps1) with 0xb5cb4 in Hms. change (SR.ps_regs PavrF6P3.ps1) with (map (fun i => (i, nth i PavrF6P3.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF6P3.ps1) with PavrF6P3.cells1 in Hcells. unfold PavrF6P3.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF6P3.regs0 PavrF6P3.regs_out1 60 KS_avrF6P3_1 KS_avrF6P3_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF6P3.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF6P3.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF6P3.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF6P3.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF6P3.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrF6P3.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PavrF6P3.regs_out1 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF6P3.regs_out1]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
Qed.

Module PavrF6P4 := BndP_Ea_063S8.LibSegEa_avrF6P4.
Definition KS_avrF6P4_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF6P4.regs0 PavrF6P4.regs_out0).
Lemma KS_avrF6P4_0_ok : BG.kept_ok 60 PavrF6P4.regs0 PavrF6P4.regs_out0 KS_avrF6P4_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avrF6P4_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF6P4.regs0 PavrF6P4.regs_out1).
Lemma KS_avrF6P4_1_ok : BG.kept_ok 60 PavrF6P4.regs0 PavrF6P4.regs_out1 KS_avrF6P4_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrF6P4_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 6) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 6) / 8) + 2147450880) 4 -> 0 <= (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7) <= 3 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb5c98 M) (st fx' R' 0xb5cdc M')
        /\ (forall x, In x KS_avrF6P4_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ getr R' (reg 11) = Z_to_bv 64 4
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb5c98 M) (st fx' R' 0xb5cb4 M')
        /\ (forall x, In x KS_avrF6P4_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ getr R' (reg 11) = Z_to_bv 64 4
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G12 G14 G15 G16 G17 G18 G19 G20 G21 G22 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavrF6P4.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrF6P4.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrF6P4.kn0).
  { unfold know_ok, PavrF6P4.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrF6P4.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrF6P4.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavrF6P4.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavrF6P4.ps0) with 0xb5cdc in Hms. change (SR.ps_regs PavrF6P4.ps0) with (map (fun i => (i, nth i PavrF6P4.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF6P4.ps0) with PavrF6P4.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF6P4.regs0 PavrF6P4.regs_out0 60 KS_avrF6P4_0 KS_avrF6P4_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF6P4.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF6P4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF6P4.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF6P4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF6P4.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrF6P4.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PavrF6P4.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF6P4.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  - right.
    change (SR.ps_pc PavrF6P4.ps1) with 0xb5cb4 in Hms. change (SR.ps_regs PavrF6P4.ps1) with (map (fun i => (i, nth i PavrF6P4.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF6P4.ps1) with PavrF6P4.cells1 in Hcells. unfold PavrF6P4.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF6P4.regs0 PavrF6P4.regs_out1 60 KS_avrF6P4_1 KS_avrF6P4_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF6P4.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF6P4.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF6P4.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF6P4.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF6P4.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrF6P4.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PavrF6P4.regs_out1 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF6P4.regs_out1]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
Qed.

Module PavrF6P5 := BndP_Ea_063S8.LibSegEa_avrF6P5.
Definition KS_avrF6P5_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF6P5.regs0 PavrF6P5.regs_out0).
Lemma KS_avrF6P5_0_ok : BG.kept_ok 60 PavrF6P5.regs0 PavrF6P5.regs_out0 KS_avrF6P5_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avrF6P5_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF6P5.regs0 PavrF6P5.regs_out1).
Lemma KS_avrF6P5_1_ok : BG.kept_ok 60 PavrF6P5.regs0 PavrF6P5.regs_out1 KS_avrF6P5_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrF6P5_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 6) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 6) / 8) + 2147450880) 5 -> 0 <= (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7) <= 4 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb5c98 M) (st fx' R' 0xb5cdc M')
        /\ (forall x, In x KS_avrF6P5_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ getr R' (reg 11) = Z_to_bv 64 5
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb5c98 M) (st fx' R' 0xb5cb4 M')
        /\ (forall x, In x KS_avrF6P5_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ getr R' (reg 11) = Z_to_bv 64 5
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G12 G14 G15 G16 G17 G18 G19 G20 G21 G22 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavrF6P5.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrF6P5.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrF6P5.kn0).
  { unfold know_ok, PavrF6P5.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrF6P5.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrF6P5.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavrF6P5.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavrF6P5.ps0) with 0xb5cdc in Hms. change (SR.ps_regs PavrF6P5.ps0) with (map (fun i => (i, nth i PavrF6P5.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF6P5.ps0) with PavrF6P5.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF6P5.regs0 PavrF6P5.regs_out0 60 KS_avrF6P5_0 KS_avrF6P5_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF6P5.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF6P5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF6P5.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF6P5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF6P5.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrF6P5.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PavrF6P5.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF6P5.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  - right.
    change (SR.ps_pc PavrF6P5.ps1) with 0xb5cb4 in Hms. change (SR.ps_regs PavrF6P5.ps1) with (map (fun i => (i, nth i PavrF6P5.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF6P5.ps1) with PavrF6P5.cells1 in Hcells. unfold PavrF6P5.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF6P5.regs0 PavrF6P5.regs_out1 60 KS_avrF6P5_1 KS_avrF6P5_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF6P5.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF6P5.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF6P5.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF6P5.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF6P5.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrF6P5.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PavrF6P5.regs_out1 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF6P5.regs_out1]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
Qed.

Module PavrF6P6 := BndP_Ea_063S8.LibSegEa_avrF6P6.
Definition KS_avrF6P6_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF6P6.regs0 PavrF6P6.regs_out0).
Lemma KS_avrF6P6_0_ok : BG.kept_ok 60 PavrF6P6.regs0 PavrF6P6.regs_out0 KS_avrF6P6_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avrF6P6_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF6P6.regs0 PavrF6P6.regs_out1).
Lemma KS_avrF6P6_1_ok : BG.kept_ok 60 PavrF6P6.regs0 PavrF6P6.regs_out1 KS_avrF6P6_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrF6P6_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 6) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 6) / 8) + 2147450880) 6 -> 0 <= (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7) <= 5 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb5c98 M) (st fx' R' 0xb5cdc M')
        /\ (forall x, In x KS_avrF6P6_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb5c98 M) (st fx' R' 0xb5cb4 M')
        /\ (forall x, In x KS_avrF6P6_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G12 G14 G15 G16 G17 G18 G19 G20 G21 G22 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavrF6P6.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrF6P6.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrF6P6.kn0).
  { unfold know_ok, PavrF6P6.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrF6P6.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrF6P6.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavrF6P6.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavrF6P6.ps0) with 0xb5cdc in Hms. change (SR.ps_regs PavrF6P6.ps0) with (map (fun i => (i, nth i PavrF6P6.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF6P6.ps0) with PavrF6P6.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF6P6.regs0 PavrF6P6.regs_out0 60 KS_avrF6P6_0 KS_avrF6P6_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF6P6.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF6P6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF6P6.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF6P6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF6P6.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrF6P6.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PavrF6P6.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF6P6.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  - right.
    change (SR.ps_pc PavrF6P6.ps1) with 0xb5cb4 in Hms. change (SR.ps_regs PavrF6P6.ps1) with (map (fun i => (i, nth i PavrF6P6.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF6P6.ps1) with PavrF6P6.cells1 in Hcells. unfold PavrF6P6.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF6P6.regs0 PavrF6P6.regs_out1 60 KS_avrF6P6_1 KS_avrF6P6_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF6P6.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF6P6.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF6P6.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF6P6.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF6P6.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrF6P6.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PavrF6P6.regs_out1 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF6P6.regs_out1]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
Qed.

Module PavrF6P7 := BndP_Ea_063S8.LibSegEa_avrF6P7.
Definition KS_avrF6P7_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF6P7.regs0 PavrF6P7.regs_out0).
Lemma KS_avrF6P7_0_ok : BG.kept_ok 60 PavrF6P7.regs0 PavrF6P7.regs_out0 KS_avrF6P7_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avrF6P7_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF6P7.regs0 PavrF6P7.regs_out1).
Lemma KS_avrF6P7_1_ok : BG.kept_ok 60 PavrF6P7.regs0 PavrF6P7.regs_out1 KS_avrF6P7_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrF6P7_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 6) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 6) / 8) + 2147450880) 7 -> 0 <= (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7) <= 6 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb5c98 M) (st fx' R' 0xb5cdc M')
        /\ (forall x, In x KS_avrF6P7_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ getr R' (reg 11) = Z_to_bv 64 7
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb5c98 M) (st fx' R' 0xb5cb4 M')
        /\ (forall x, In x KS_avrF6P7_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ getr R' (reg 11) = Z_to_bv 64 7
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G12 G14 G15 G16 G17 G18 G19 G20 G21 G22 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavrF6P7.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrF6P7.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrF6P7.kn0).
  { unfold know_ok, PavrF6P7.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrF6P7.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrF6P7.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavrF6P7.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavrF6P7.ps0) with 0xb5cdc in Hms. change (SR.ps_regs PavrF6P7.ps0) with (map (fun i => (i, nth i PavrF6P7.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF6P7.ps0) with PavrF6P7.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF6P7.regs0 PavrF6P7.regs_out0 60 KS_avrF6P7_0 KS_avrF6P7_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF6P7.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF6P7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF6P7.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF6P7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF6P7.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrF6P7.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PavrF6P7.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF6P7.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  - right.
    change (SR.ps_pc PavrF6P7.ps1) with 0xb5cb4 in Hms. change (SR.ps_regs PavrF6P7.ps1) with (map (fun i => (i, nth i PavrF6P7.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF6P7.ps1) with PavrF6P7.cells1 in Hcells. unfold PavrF6P7.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF6P7.regs0 PavrF6P7.regs_out1 60 KS_avrF6P7_1 KS_avrF6P7_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF6P7.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF6P7.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF6P7.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF6P7.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF6P7.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrF6P7.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PavrF6P7.regs_out1 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF6P7.regs_out1]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
Qed.

Module PavrF7Z := BndP_Ea_064S8.LibSegEa_avrF7Z.
Definition KS_avrF7Z_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF7Z.regs0 PavrF7Z.regs_out0).
Lemma KS_avrF7Z_0_ok : BG.kept_ok 60 PavrF7Z.regs0 PavrF7Z.regs_out0 KS_avrF7Z_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avrF7Z_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF7Z.regs0 PavrF7Z.regs_out1).
Lemma KS_avrF7Z_1_ok : BG.kept_ok 60 PavrF7Z.regs0 PavrF7Z.regs_out1 KS_avrF7Z_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrF7Z_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 7) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5KA.zeros_at M ((((V 33%nat) + 7) / 8) + 2147450880) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb5cb4 M) (st fx' R' 0xb5cdc M')
        /\ (forall x, In x KS_avrF7Z_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb5cb4 M) (st fx' R' 0xb5dd4 M')
        /\ (forall x, In x KS_avrF7Z_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + 8)
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
  assert (HR: regs_ok E PavrF7Z.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrF7Z.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrF7Z.kn0).
  { unfold know_ok, PavrF7Z.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrF7Z.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrF7Z.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavrF7Z.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavrF7Z.ps0) with 0xb5cdc in Hms. change (SR.ps_regs PavrF7Z.ps0) with (map (fun i => (i, nth i PavrF7Z.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF7Z.ps0) with PavrF7Z.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF7Z.regs0 PavrF7Z.regs_out0 60 KS_avrF7Z_0 KS_avrF7Z_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF7Z.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF7Z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF7Z.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF7Z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF7Z.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF7Z.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  - right.
    change (SR.ps_pc PavrF7Z.ps1) with 0xb5dd4 in Hms. change (SR.ps_regs PavrF7Z.ps1) with (map (fun i => (i, nth i PavrF7Z.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF7Z.ps1) with PavrF7Z.cells1 in Hcells. unfold PavrF7Z.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF7Z.regs0 PavrF7Z.regs_out1 60 KS_avrF7Z_1 KS_avrF7Z_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF7Z.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF7Z.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF7Z.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF7Z.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF7Z.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PavrF7Z.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF7Z.regs_out1 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF7Z.regs_out1]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
Qed.

Module PavrF7P1 := BndP_Ea_063S8.LibSegEa_avrF7P1.
Definition KS_avrF7P1_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF7P1.regs0 PavrF7P1.regs_out0).
Lemma KS_avrF7P1_0_ok : BG.kept_ok 60 PavrF7P1.regs0 PavrF7P1.regs_out0 KS_avrF7P1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avrF7P1_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF7P1.regs0 PavrF7P1.regs_out1).
Lemma KS_avrF7P1_1_ok : BG.kept_ok 60 PavrF7P1.regs0 PavrF7P1.regs_out1 KS_avrF7P1_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrF7P1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 7) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 7) / 8) + 2147450880) 1 -> 0 <= (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7) <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb5cb4 M) (st fx' R' 0xb5cdc M')
        /\ (forall x, In x KS_avrF7P1_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb5cb4 M) (st fx' R' 0xb5dd4 M')
        /\ (forall x, In x KS_avrF7P1_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G12 G14 G15 G16 G17 G18 G19 G20 G21 G22 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavrF7P1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrF7P1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrF7P1.kn0).
  { unfold know_ok, PavrF7P1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrF7P1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrF7P1.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavrF7P1.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavrF7P1.ps0) with 0xb5cdc in Hms. change (SR.ps_regs PavrF7P1.ps0) with (map (fun i => (i, nth i PavrF7P1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF7P1.ps0) with PavrF7P1.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF7P1.regs0 PavrF7P1.regs_out0 60 KS_avrF7P1_0 KS_avrF7P1_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF7P1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF7P1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF7P1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF7P1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF7P1.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrF7P1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF7P1.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF7P1.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  - right.
    change (SR.ps_pc PavrF7P1.ps1) with 0xb5dd4 in Hms. change (SR.ps_regs PavrF7P1.ps1) with (map (fun i => (i, nth i PavrF7P1.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF7P1.ps1) with PavrF7P1.cells1 in Hcells. unfold PavrF7P1.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF7P1.regs0 PavrF7P1.regs_out1 60 KS_avrF7P1_1 KS_avrF7P1_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF7P1.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF7P1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF7P1.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF7P1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF7P1.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PavrF7P1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF7P1.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrF7P1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF7P1.regs_out1 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF7P1.regs_out1]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
Qed.

Module PavrF7P2 := BndP_Ea_063S8.LibSegEa_avrF7P2.
Definition KS_avrF7P2_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF7P2.regs0 PavrF7P2.regs_out0).
Lemma KS_avrF7P2_0_ok : BG.kept_ok 60 PavrF7P2.regs0 PavrF7P2.regs_out0 KS_avrF7P2_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avrF7P2_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF7P2.regs0 PavrF7P2.regs_out1).
Lemma KS_avrF7P2_1_ok : BG.kept_ok 60 PavrF7P2.regs0 PavrF7P2.regs_out1 KS_avrF7P2_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrF7P2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 7) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 7) / 8) + 2147450880) 2 -> 0 <= (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb5cb4 M) (st fx' R' 0xb5cdc M')
        /\ (forall x, In x KS_avrF7P2_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb5cb4 M) (st fx' R' 0xb5dd4 M')
        /\ (forall x, In x KS_avrF7P2_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G12 G14 G15 G16 G17 G18 G19 G20 G21 G22 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavrF7P2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrF7P2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrF7P2.kn0).
  { unfold know_ok, PavrF7P2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrF7P2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrF7P2.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavrF7P2.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavrF7P2.ps0) with 0xb5cdc in Hms. change (SR.ps_regs PavrF7P2.ps0) with (map (fun i => (i, nth i PavrF7P2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF7P2.ps0) with PavrF7P2.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF7P2.regs0 PavrF7P2.regs_out0 60 KS_avrF7P2_0 KS_avrF7P2_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF7P2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF7P2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF7P2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF7P2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF7P2.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrF7P2.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PavrF7P2.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF7P2.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  - right.
    change (SR.ps_pc PavrF7P2.ps1) with 0xb5dd4 in Hms. change (SR.ps_regs PavrF7P2.ps1) with (map (fun i => (i, nth i PavrF7P2.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF7P2.ps1) with PavrF7P2.cells1 in Hcells. unfold PavrF7P2.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF7P2.regs0 PavrF7P2.regs_out1 60 KS_avrF7P2_1 KS_avrF7P2_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF7P2.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF7P2.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF7P2.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF7P2.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF7P2.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PavrF7P2.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF7P2.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrF7P2.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PavrF7P2.regs_out1 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF7P2.regs_out1]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
Qed.

Module PavrF7P3 := BndP_Ea_063S8.LibSegEa_avrF7P3.
Definition KS_avrF7P3_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF7P3.regs0 PavrF7P3.regs_out0).
Lemma KS_avrF7P3_0_ok : BG.kept_ok 60 PavrF7P3.regs0 PavrF7P3.regs_out0 KS_avrF7P3_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avrF7P3_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF7P3.regs0 PavrF7P3.regs_out1).
Lemma KS_avrF7P3_1_ok : BG.kept_ok 60 PavrF7P3.regs0 PavrF7P3.regs_out1 KS_avrF7P3_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrF7P3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 7) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 7) / 8) + 2147450880) 3 -> 0 <= (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7) <= 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb5cb4 M) (st fx' R' 0xb5cdc M')
        /\ (forall x, In x KS_avrF7P3_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ getr R' (reg 11) = Z_to_bv 64 3
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb5cb4 M) (st fx' R' 0xb5dd4 M')
        /\ (forall x, In x KS_avrF7P3_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ getr R' (reg 11) = Z_to_bv 64 3
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G12 G14 G15 G16 G17 G18 G19 G20 G21 G22 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavrF7P3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrF7P3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrF7P3.kn0).
  { unfold know_ok, PavrF7P3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrF7P3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrF7P3.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavrF7P3.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavrF7P3.ps0) with 0xb5cdc in Hms. change (SR.ps_regs PavrF7P3.ps0) with (map (fun i => (i, nth i PavrF7P3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF7P3.ps0) with PavrF7P3.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF7P3.regs0 PavrF7P3.regs_out0 60 KS_avrF7P3_0 KS_avrF7P3_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF7P3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF7P3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF7P3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF7P3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF7P3.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrF7P3.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PavrF7P3.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF7P3.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  - right.
    change (SR.ps_pc PavrF7P3.ps1) with 0xb5dd4 in Hms. change (SR.ps_regs PavrF7P3.ps1) with (map (fun i => (i, nth i PavrF7P3.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF7P3.ps1) with PavrF7P3.cells1 in Hcells. unfold PavrF7P3.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF7P3.regs0 PavrF7P3.regs_out1 60 KS_avrF7P3_1 KS_avrF7P3_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF7P3.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF7P3.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF7P3.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF7P3.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF7P3.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PavrF7P3.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF7P3.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrF7P3.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PavrF7P3.regs_out1 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF7P3.regs_out1]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
Qed.

Module PavrF7P4 := BndP_Ea_063S8.LibSegEa_avrF7P4.
Definition KS_avrF7P4_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF7P4.regs0 PavrF7P4.regs_out0).
Lemma KS_avrF7P4_0_ok : BG.kept_ok 60 PavrF7P4.regs0 PavrF7P4.regs_out0 KS_avrF7P4_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avrF7P4_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF7P4.regs0 PavrF7P4.regs_out1).
Lemma KS_avrF7P4_1_ok : BG.kept_ok 60 PavrF7P4.regs0 PavrF7P4.regs_out1 KS_avrF7P4_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrF7P4_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 7) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 7) / 8) + 2147450880) 4 -> 0 <= (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7) <= 3 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb5cb4 M) (st fx' R' 0xb5cdc M')
        /\ (forall x, In x KS_avrF7P4_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ getr R' (reg 11) = Z_to_bv 64 4
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb5cb4 M) (st fx' R' 0xb5dd4 M')
        /\ (forall x, In x KS_avrF7P4_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ getr R' (reg 11) = Z_to_bv 64 4
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G12 G14 G15 G16 G17 G18 G19 G20 G21 G22 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavrF7P4.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrF7P4.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrF7P4.kn0).
  { unfold know_ok, PavrF7P4.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrF7P4.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrF7P4.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavrF7P4.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavrF7P4.ps0) with 0xb5cdc in Hms. change (SR.ps_regs PavrF7P4.ps0) with (map (fun i => (i, nth i PavrF7P4.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF7P4.ps0) with PavrF7P4.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF7P4.regs0 PavrF7P4.regs_out0 60 KS_avrF7P4_0 KS_avrF7P4_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF7P4.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF7P4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF7P4.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF7P4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF7P4.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrF7P4.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PavrF7P4.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF7P4.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  - right.
    change (SR.ps_pc PavrF7P4.ps1) with 0xb5dd4 in Hms. change (SR.ps_regs PavrF7P4.ps1) with (map (fun i => (i, nth i PavrF7P4.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF7P4.ps1) with PavrF7P4.cells1 in Hcells. unfold PavrF7P4.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF7P4.regs0 PavrF7P4.regs_out1 60 KS_avrF7P4_1 KS_avrF7P4_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF7P4.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF7P4.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF7P4.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF7P4.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF7P4.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PavrF7P4.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF7P4.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrF7P4.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PavrF7P4.regs_out1 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF7P4.regs_out1]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
Qed.

Module PavrF7P5 := BndP_Ea_063S8.LibSegEa_avrF7P5.
Definition KS_avrF7P5_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF7P5.regs0 PavrF7P5.regs_out0).
Lemma KS_avrF7P5_0_ok : BG.kept_ok 60 PavrF7P5.regs0 PavrF7P5.regs_out0 KS_avrF7P5_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avrF7P5_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF7P5.regs0 PavrF7P5.regs_out1).
Lemma KS_avrF7P5_1_ok : BG.kept_ok 60 PavrF7P5.regs0 PavrF7P5.regs_out1 KS_avrF7P5_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrF7P5_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 7) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 7) / 8) + 2147450880) 5 -> 0 <= (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7) <= 4 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb5cb4 M) (st fx' R' 0xb5cdc M')
        /\ (forall x, In x KS_avrF7P5_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ getr R' (reg 11) = Z_to_bv 64 5
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb5cb4 M) (st fx' R' 0xb5dd4 M')
        /\ (forall x, In x KS_avrF7P5_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ getr R' (reg 11) = Z_to_bv 64 5
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G12 G14 G15 G16 G17 G18 G19 G20 G21 G22 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavrF7P5.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrF7P5.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrF7P5.kn0).
  { unfold know_ok, PavrF7P5.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrF7P5.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrF7P5.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavrF7P5.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavrF7P5.ps0) with 0xb5cdc in Hms. change (SR.ps_regs PavrF7P5.ps0) with (map (fun i => (i, nth i PavrF7P5.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF7P5.ps0) with PavrF7P5.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF7P5.regs0 PavrF7P5.regs_out0 60 KS_avrF7P5_0 KS_avrF7P5_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF7P5.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF7P5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF7P5.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF7P5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF7P5.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrF7P5.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PavrF7P5.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF7P5.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  - right.
    change (SR.ps_pc PavrF7P5.ps1) with 0xb5dd4 in Hms. change (SR.ps_regs PavrF7P5.ps1) with (map (fun i => (i, nth i PavrF7P5.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF7P5.ps1) with PavrF7P5.cells1 in Hcells. unfold PavrF7P5.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF7P5.regs0 PavrF7P5.regs_out1 60 KS_avrF7P5_1 KS_avrF7P5_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF7P5.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF7P5.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF7P5.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF7P5.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF7P5.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PavrF7P5.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF7P5.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrF7P5.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PavrF7P5.regs_out1 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF7P5.regs_out1]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
Qed.

Module PavrF7P6 := BndP_Ea_063S8.LibSegEa_avrF7P6.
Definition KS_avrF7P6_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF7P6.regs0 PavrF7P6.regs_out0).
Lemma KS_avrF7P6_0_ok : BG.kept_ok 60 PavrF7P6.regs0 PavrF7P6.regs_out0 KS_avrF7P6_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avrF7P6_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF7P6.regs0 PavrF7P6.regs_out1).
Lemma KS_avrF7P6_1_ok : BG.kept_ok 60 PavrF7P6.regs0 PavrF7P6.regs_out1 KS_avrF7P6_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrF7P6_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 7) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 7) / 8) + 2147450880) 6 -> 0 <= (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7) <= 5 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb5cb4 M) (st fx' R' 0xb5cdc M')
        /\ (forall x, In x KS_avrF7P6_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb5cb4 M) (st fx' R' 0xb5dd4 M')
        /\ (forall x, In x KS_avrF7P6_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G12 G14 G15 G16 G17 G18 G19 G20 G21 G22 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavrF7P6.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrF7P6.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrF7P6.kn0).
  { unfold know_ok, PavrF7P6.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrF7P6.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrF7P6.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavrF7P6.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavrF7P6.ps0) with 0xb5cdc in Hms. change (SR.ps_regs PavrF7P6.ps0) with (map (fun i => (i, nth i PavrF7P6.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF7P6.ps0) with PavrF7P6.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF7P6.regs0 PavrF7P6.regs_out0 60 KS_avrF7P6_0 KS_avrF7P6_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF7P6.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF7P6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF7P6.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF7P6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF7P6.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrF7P6.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PavrF7P6.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF7P6.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  - right.
    change (SR.ps_pc PavrF7P6.ps1) with 0xb5dd4 in Hms. change (SR.ps_regs PavrF7P6.ps1) with (map (fun i => (i, nth i PavrF7P6.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF7P6.ps1) with PavrF7P6.cells1 in Hcells. unfold PavrF7P6.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF7P6.regs0 PavrF7P6.regs_out1 60 KS_avrF7P6_1 KS_avrF7P6_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF7P6.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF7P6.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF7P6.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF7P6.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF7P6.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PavrF7P6.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF7P6.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrF7P6.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PavrF7P6.regs_out1 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF7P6.regs_out1]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
Qed.

Module PavrF7P7 := BndP_Ea_064S8.LibSegEa_avrF7P7.
Definition KS_avrF7P7_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF7P7.regs0 PavrF7P7.regs_out0).
Lemma KS_avrF7P7_0_ok : BG.kept_ok 60 PavrF7P7.regs0 PavrF7P7.regs_out0 KS_avrF7P7_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avrF7P7_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF7P7.regs0 PavrF7P7.regs_out1).
Lemma KS_avrF7P7_1_ok : BG.kept_ok 60 PavrF7P7.regs0 PavrF7P7.regs_out1 KS_avrF7P7_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avrF7P7_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 7) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 7) / 8) + 2147450880) 7 -> 0 <= (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7) <= 6 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb5cb4 M) (st fx' R' 0xb5cdc M')
        /\ (forall x, In x KS_avrF7P7_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ getr R' (reg 11) = Z_to_bv 64 7
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb5cb4 M) (st fx' R' 0xb5dd4 M')
        /\ (forall x, In x KS_avrF7P7_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ getr R' (reg 11) = Z_to_bv 64 7
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G8 G9 G12 G14 G15 G16 G17 G18 G19 G20 G21 G22 G28 G29 G30 G31 pvzI5 pvzI6 pvzI7 K3 pvzI8 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PavrF7P7.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavrF7P7.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavrF7P7.kn0).
  { unfold know_ok, PavrF7P7.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K1l K1r K2l K2r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r HV35l HV35r K1l K1r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear - HV36l HV36r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K2l K2r; lia | clear - HV33l HV33r K0l K0r K2l K2r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavrF7P7.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavrF7P7.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavrF7P7.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PavrF7P7.ps0) with 0xb5cdc in Hms. change (SR.ps_regs PavrF7P7.ps0) with (map (fun i => (i, nth i PavrF7P7.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF7P7.ps0) with PavrF7P7.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF7P7.regs0 PavrF7P7.regs_out0 60 KS_avrF7P7_0 KS_avrF7P7_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF7P7.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF7P7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF7P7.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF7P7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF7P7.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrF7P7.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PavrF7P7.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF7P7.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  - right.
    change (SR.ps_pc PavrF7P7.ps1) with 0xb5dd4 in Hms. change (SR.ps_regs PavrF7P7.ps1) with (map (fun i => (i, nth i PavrF7P7.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavrF7P7.ps1) with PavrF7P7.cells1 in Hcells. unfold PavrF7P7.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavrF7P7.regs0 PavrF7P7.regs_out1 60 KS_avrF7P7_1 KS_avrF7P7_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavrF7P7.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PavrF7P7.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF7P7.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavrF7P7.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF7P7.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PavrF7P7.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavrF7P7.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PavrF7P7.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PavrF7P7.regs_out1 E' R' 23 Hregs) by (clear; lia). cbn [nth PavrF7P7.regs_out1]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). subst E; reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
Qed.

End PECVALARP3.
