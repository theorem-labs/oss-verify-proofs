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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.seg Require BndP_Ea_045S8 BndP_Ea_046S8.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEARVP2.
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

Module ParvX69 := BndP_Ea_045S8.LibSegEa_arvX69.
Definition KS_arvX69 : list nat := Eval vm_compute in (BG.kept_list 72 ParvX69.regs0 ParvX69.regs_out0).
Lemma KS_arvX69_ok : BG.kept_ok 72 ParvX69.regs0 ParvX69.regs_out0 KS_arvX69 = true. Proof. vm_compute. reflexivity. Qed.
Lemma arvX69_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 12) = Z_to_bv 64 99 -> getr R (reg 18) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 47%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 (V 37%nat) -> getr R (reg 23) = Z_to_bv 64 69 -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 47%nat) ->
  L5.img_clear M 65536 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6914048 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 128)) -> 6914048 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 128) + 128 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 128)) ->
  ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3aec M) (st fx' R' 0xae310 M')
        /\ (forall x, In x KS_arvX69 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 738448
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 6).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G12 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI6 K4 K5 pvzI7 K7 K8 K9 K10 K11 K12 K13 pvzI8 K15 K16 K17 K18 K19 K20.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K6l; move K6l before pvzI7; pose proof (proj2 pvzI7) as K6r; move K6r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K14l; move K14l before pvzI8; pose proof (proj2 pvzI8) as K14r; move K14r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 48%nat. }
  assert (HR: regs_ok E ParvX69.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParvX69.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParvX69.kn0).
  { unfold know_ok, ParvX69.kn0.
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
  pvz_hg ltac:(idtac; destruct (ParvX69.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParvX69.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold ParvX69.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc ParvX69.ps0) with 0xae310 in Hms. change (SR.ps_regs ParvX69.ps0) with (map (fun i => (i, nth i ParvX69.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells ParvX69.ps0) with ParvX69.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' ParvX69.regs0 ParvX69.regs_out0 72 KS_arvX69 KS_arvX69_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg ParvX69.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth ParvX69.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvX69.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParvX69.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg ParvX69.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParvX69.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module ParvX71 := BndP_Ea_045S8.LibSegEa_arvX71.
Definition KS_arvX71 : list nat := Eval vm_compute in (BG.kept_list 72 ParvX71.regs0 ParvX71.regs_out0).
Lemma KS_arvX71_ok : BG.kept_ok 72 ParvX71.regs0 ParvX71.regs_out0 KS_arvX71 = true. Proof. vm_compute. reflexivity. Qed.
Lemma arvX71_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 12) = Z_to_bv 64 99 -> getr R (reg 18) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 47%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 (V 37%nat) -> getr R (reg 23) = Z_to_bv 64 71 -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 47%nat) ->
  L5.img_clear M 65536 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6914048 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 128)) -> 6914048 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 128) + 128 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 128)) ->
  ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3aec M) (st fx' R' 0xae310 M')
        /\ (forall x, In x KS_arvX71 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 738448
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 6).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G12 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI6 K4 K5 pvzI7 K7 K8 K9 K10 K11 K12 K13 pvzI8 K15 K16 K17 K18 K19 K20.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K6l; move K6l before pvzI7; pose proof (proj2 pvzI7) as K6r; move K6r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K14l; move K14l before pvzI8; pose proof (proj2 pvzI8) as K14r; move K14r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 48%nat. }
  assert (HR: regs_ok E ParvX71.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParvX71.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParvX71.kn0).
  { unfold know_ok, ParvX71.kn0.
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
  pvz_hg ltac:(idtac; destruct (ParvX71.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParvX71.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold ParvX71.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc ParvX71.ps0) with 0xae310 in Hms. change (SR.ps_regs ParvX71.ps0) with (map (fun i => (i, nth i ParvX71.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells ParvX71.ps0) with ParvX71.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' ParvX71.regs0 ParvX71.regs_out0 72 KS_arvX71 KS_arvX71_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg ParvX71.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth ParvX71.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvX71.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParvX71.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg ParvX71.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParvX71.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module ParvX74 := BndP_Ea_045S8.LibSegEa_arvX74.
Definition KS_arvX74 : list nat := Eval vm_compute in (BG.kept_list 72 ParvX74.regs0 ParvX74.regs_out0).
Lemma KS_arvX74_ok : BG.kept_ok 72 ParvX74.regs0 ParvX74.regs_out0 KS_arvX74 = true. Proof. vm_compute. reflexivity. Qed.
Lemma arvX74_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 12) = Z_to_bv 64 99 -> getr R (reg 18) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 47%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 (V 37%nat) -> getr R (reg 23) = Z_to_bv 64 74 -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 47%nat) ->
  L5.img_clear M 65536 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6914048 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 128)) -> 6914048 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 128) + 128 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 128)) ->
  ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3aec M) (st fx' R' 0xae310 M')
        /\ (forall x, In x KS_arvX74 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 738448
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 6).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G12 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI6 K4 K5 pvzI7 K7 K8 K9 K10 K11 K12 K13 pvzI8 K15 K16 K17 K18 K19 K20.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K6l; move K6l before pvzI7; pose proof (proj2 pvzI7) as K6r; move K6r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K14l; move K14l before pvzI8; pose proof (proj2 pvzI8) as K14r; move K14r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 48%nat. }
  assert (HR: regs_ok E ParvX74.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParvX74.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParvX74.kn0).
  { unfold know_ok, ParvX74.kn0.
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
  pvz_hg ltac:(idtac; destruct (ParvX74.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParvX74.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold ParvX74.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc ParvX74.ps0) with 0xae310 in Hms. change (SR.ps_regs ParvX74.ps0) with (map (fun i => (i, nth i ParvX74.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells ParvX74.ps0) with ParvX74.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' ParvX74.regs0 ParvX74.regs_out0 72 KS_arvX74 KS_arvX74_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg ParvX74.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth ParvX74.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvX74.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParvX74.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg ParvX74.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParvX74.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module ParvX75 := BndP_Ea_045S8.LibSegEa_arvX75.
Definition KS_arvX75 : list nat := Eval vm_compute in (BG.kept_list 72 ParvX75.regs0 ParvX75.regs_out0).
Lemma KS_arvX75_ok : BG.kept_ok 72 ParvX75.regs0 ParvX75.regs_out0 KS_arvX75 = true. Proof. vm_compute. reflexivity. Qed.
Lemma arvX75_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 12) = Z_to_bv 64 99 -> getr R (reg 18) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 47%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 (V 37%nat) -> getr R (reg 23) = Z_to_bv 64 75 -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 47%nat) ->
  L5.img_clear M 65536 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6914048 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 128)) -> 6914048 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 128) + 128 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 128)) ->
  ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3aec M) (st fx' R' 0xae310 M')
        /\ (forall x, In x KS_arvX75 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 738448
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 6).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G12 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI6 K4 K5 pvzI7 K7 K8 K9 K10 K11 K12 K13 pvzI8 K15 K16 K17 K18 K19 K20.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K6l; move K6l before pvzI7; pose proof (proj2 pvzI7) as K6r; move K6r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K14l; move K14l before pvzI8; pose proof (proj2 pvzI8) as K14r; move K14r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 48%nat. }
  assert (HR: regs_ok E ParvX75.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParvX75.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParvX75.kn0).
  { unfold know_ok, ParvX75.kn0.
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
  pvz_hg ltac:(idtac; destruct (ParvX75.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParvX75.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold ParvX75.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc ParvX75.ps0) with 0xae310 in Hms. change (SR.ps_regs ParvX75.ps0) with (map (fun i => (i, nth i ParvX75.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells ParvX75.ps0) with ParvX75.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' ParvX75.regs0 ParvX75.regs_out0 72 KS_arvX75 KS_arvX75_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg ParvX75.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth ParvX75.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvX75.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParvX75.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg ParvX75.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParvX75.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module ParvX77 := BndP_Ea_045S8.LibSegEa_arvX77.
Definition KS_arvX77 : list nat := Eval vm_compute in (BG.kept_list 72 ParvX77.regs0 ParvX77.regs_out0).
Lemma KS_arvX77_ok : BG.kept_ok 72 ParvX77.regs0 ParvX77.regs_out0 KS_arvX77 = true. Proof. vm_compute. reflexivity. Qed.
Lemma arvX77_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 12) = Z_to_bv 64 99 -> getr R (reg 18) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 47%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 (V 37%nat) -> getr R (reg 23) = Z_to_bv 64 77 -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 47%nat) ->
  L5.img_clear M 65536 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6914048 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 128)) -> 6914048 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 128) + 128 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 128)) ->
  ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3aec M) (st fx' R' 0xae310 M')
        /\ (forall x, In x KS_arvX77 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 738448
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 6).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G12 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI6 K4 K5 pvzI7 K7 K8 K9 K10 K11 K12 K13 pvzI8 K15 K16 K17 K18 K19 K20.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K6l; move K6l before pvzI7; pose proof (proj2 pvzI7) as K6r; move K6r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K14l; move K14l before pvzI8; pose proof (proj2 pvzI8) as K14r; move K14r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 48%nat. }
  assert (HR: regs_ok E ParvX77.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParvX77.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParvX77.kn0).
  { unfold know_ok, ParvX77.kn0.
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
  pvz_hg ltac:(idtac; destruct (ParvX77.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParvX77.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold ParvX77.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc ParvX77.ps0) with 0xae310 in Hms. change (SR.ps_regs ParvX77.ps0) with (map (fun i => (i, nth i ParvX77.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells ParvX77.ps0) with ParvX77.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' ParvX77.regs0 ParvX77.regs_out0 72 KS_arvX77 KS_arvX77_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg ParvX77.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth ParvX77.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvX77.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParvX77.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg ParvX77.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParvX77.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module ParvX79 := BndP_Ea_045S8.LibSegEa_arvX79.
Definition KS_arvX79 : list nat := Eval vm_compute in (BG.kept_list 72 ParvX79.regs0 ParvX79.regs_out0).
Lemma KS_arvX79_ok : BG.kept_ok 72 ParvX79.regs0 ParvX79.regs_out0 KS_arvX79 = true. Proof. vm_compute. reflexivity. Qed.
Lemma arvX79_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 12) = Z_to_bv 64 99 -> getr R (reg 18) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 47%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 (V 37%nat) -> getr R (reg 23) = Z_to_bv 64 79 -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 47%nat) ->
  L5.img_clear M 65536 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6914048 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 128)) -> 6914048 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 128) + 128 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 128)) ->
  ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3aec M) (st fx' R' 0xae310 M')
        /\ (forall x, In x KS_arvX79 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 738448
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 6).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G12 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI6 K4 K5 pvzI7 K7 K8 K9 K10 K11 K12 K13 pvzI8 K15 K16 K17 K18 K19 K20.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K6l; move K6l before pvzI7; pose proof (proj2 pvzI7) as K6r; move K6r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K14l; move K14l before pvzI8; pose proof (proj2 pvzI8) as K14r; move K14r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 48%nat. }
  assert (HR: regs_ok E ParvX79.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParvX79.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParvX79.kn0).
  { unfold know_ok, ParvX79.kn0.
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
  pvz_hg ltac:(idtac; destruct (ParvX79.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParvX79.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold ParvX79.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc ParvX79.ps0) with 0xae310 in Hms. change (SR.ps_regs ParvX79.ps0) with (map (fun i => (i, nth i ParvX79.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells ParvX79.ps0) with ParvX79.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' ParvX79.regs0 ParvX79.regs_out0 72 KS_arvX79 KS_arvX79_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg ParvX79.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth ParvX79.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvX79.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParvX79.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg ParvX79.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParvX79.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module ParvX80 := BndP_Ea_045S8.LibSegEa_arvX80.
Definition KS_arvX80 : list nat := Eval vm_compute in (BG.kept_list 72 ParvX80.regs0 ParvX80.regs_out0).
Lemma KS_arvX80_ok : BG.kept_ok 72 ParvX80.regs0 ParvX80.regs_out0 KS_arvX80 = true. Proof. vm_compute. reflexivity. Qed.
Lemma arvX80_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 12) = Z_to_bv 64 99 -> getr R (reg 18) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 47%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 (V 37%nat) -> getr R (reg 23) = Z_to_bv 64 80 -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 47%nat) ->
  L5.img_clear M 65536 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6914048 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 128)) -> 6914048 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 128) + 128 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 128)) ->
  ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3aec M) (st fx' R' 0xae310 M')
        /\ (forall x, In x KS_arvX80 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 738448
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 6).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G12 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI6 K4 K5 pvzI7 K7 K8 K9 K10 K11 K12 K13 pvzI8 K15 K16 K17 K18 K19 K20.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K6l; move K6l before pvzI7; pose proof (proj2 pvzI7) as K6r; move K6r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K14l; move K14l before pvzI8; pose proof (proj2 pvzI8) as K14r; move K14r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 48%nat. }
  assert (HR: regs_ok E ParvX80.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParvX80.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParvX80.kn0).
  { unfold know_ok, ParvX80.kn0.
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
  pvz_hg ltac:(idtac; destruct (ParvX80.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParvX80.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold ParvX80.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc ParvX80.ps0) with 0xae310 in Hms. change (SR.ps_regs ParvX80.ps0) with (map (fun i => (i, nth i ParvX80.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells ParvX80.ps0) with ParvX80.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' ParvX80.regs0 ParvX80.regs_out0 72 KS_arvX80 KS_arvX80_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg ParvX80.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth ParvX80.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvX80.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParvX80.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg ParvX80.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParvX80.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module ParvX81 := BndP_Ea_045S8.LibSegEa_arvX81.
Definition KS_arvX81 : list nat := Eval vm_compute in (BG.kept_list 72 ParvX81.regs0 ParvX81.regs_out0).
Lemma KS_arvX81_ok : BG.kept_ok 72 ParvX81.regs0 ParvX81.regs_out0 KS_arvX81 = true. Proof. vm_compute. reflexivity. Qed.
Lemma arvX81_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 12) = Z_to_bv 64 99 -> getr R (reg 18) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 47%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 (V 37%nat) -> getr R (reg 23) = Z_to_bv 64 81 -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 47%nat) ->
  L5.img_clear M 65536 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6914048 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 128)) -> 6914048 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 128) + 128 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 128)) ->
  ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3aec M) (st fx' R' 0xae310 M')
        /\ (forall x, In x KS_arvX81 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 738448
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 6).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G12 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI6 K4 K5 pvzI7 K7 K8 K9 K10 K11 K12 K13 pvzI8 K15 K16 K17 K18 K19 K20.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K6l; move K6l before pvzI7; pose proof (proj2 pvzI7) as K6r; move K6r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K14l; move K14l before pvzI8; pose proof (proj2 pvzI8) as K14r; move K14r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 48%nat. }
  assert (HR: regs_ok E ParvX81.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParvX81.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParvX81.kn0).
  { unfold know_ok, ParvX81.kn0.
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
  pvz_hg ltac:(idtac; destruct (ParvX81.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParvX81.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold ParvX81.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc ParvX81.ps0) with 0xae310 in Hms. change (SR.ps_regs ParvX81.ps0) with (map (fun i => (i, nth i ParvX81.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells ParvX81.ps0) with ParvX81.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' ParvX81.regs0 ParvX81.regs_out0 72 KS_arvX81 KS_arvX81_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg ParvX81.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth ParvX81.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvX81.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParvX81.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg ParvX81.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParvX81.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module ParvX82 := BndP_Ea_045S8.LibSegEa_arvX82.
Definition KS_arvX82 : list nat := Eval vm_compute in (BG.kept_list 72 ParvX82.regs0 ParvX82.regs_out0).
Lemma KS_arvX82_ok : BG.kept_ok 72 ParvX82.regs0 ParvX82.regs_out0 KS_arvX82 = true. Proof. vm_compute. reflexivity. Qed.
Lemma arvX82_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 12) = Z_to_bv 64 99 -> getr R (reg 18) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 47%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 (V 37%nat) -> getr R (reg 23) = Z_to_bv 64 82 -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 47%nat) ->
  L5.img_clear M 65536 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6914048 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 128)) -> 6914048 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 128) + 128 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 128)) ->
  ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3aec M) (st fx' R' 0xae310 M')
        /\ (forall x, In x KS_arvX82 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 738448
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 6).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G12 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI6 K4 K5 pvzI7 K7 K8 K9 K10 K11 K12 K13 pvzI8 K15 K16 K17 K18 K19 K20.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K6l; move K6l before pvzI7; pose proof (proj2 pvzI7) as K6r; move K6r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K14l; move K14l before pvzI8; pose proof (proj2 pvzI8) as K14r; move K14r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 48%nat. }
  assert (HR: regs_ok E ParvX82.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParvX82.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParvX82.kn0).
  { unfold know_ok, ParvX82.kn0.
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
  pvz_hg ltac:(idtac; destruct (ParvX82.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParvX82.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold ParvX82.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc ParvX82.ps0) with 0xae310 in Hms. change (SR.ps_regs ParvX82.ps0) with (map (fun i => (i, nth i ParvX82.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells ParvX82.ps0) with ParvX82.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' ParvX82.regs0 ParvX82.regs_out0 72 KS_arvX82 KS_arvX82_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg ParvX82.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth ParvX82.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvX82.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParvX82.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg ParvX82.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParvX82.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module ParvX86 := BndP_Ea_046S8.LibSegEa_arvX86.
Definition KS_arvX86 : list nat := Eval vm_compute in (BG.kept_list 72 ParvX86.regs0 ParvX86.regs_out0).
Lemma KS_arvX86_ok : BG.kept_ok 72 ParvX86.regs0 ParvX86.regs_out0 KS_arvX86 = true. Proof. vm_compute. reflexivity. Qed.
Lemma arvX86_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 12) = Z_to_bv 64 99 -> getr R (reg 18) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 47%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 (V 37%nat) -> getr R (reg 23) = Z_to_bv 64 86 -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 47%nat) ->
  L5.img_clear M 65536 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6914048 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 128)) -> 6914048 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 128) + 128 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 128)) ->
  ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3aec M) (st fx' R' 0xae310 M')
        /\ (forall x, In x KS_arvX86 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 738448
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 6).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G12 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI6 K4 K5 pvzI7 K7 K8 K9 K10 K11 K12 K13 pvzI8 K15 K16 K17 K18 K19 K20.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K6l; move K6l before pvzI7; pose proof (proj2 pvzI7) as K6r; move K6r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K14l; move K14l before pvzI8; pose proof (proj2 pvzI8) as K14r; move K14r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 48%nat. }
  assert (HR: regs_ok E ParvX86.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParvX86.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParvX86.kn0).
  { unfold know_ok, ParvX86.kn0.
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
  pvz_hg ltac:(idtac; destruct (ParvX86.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParvX86.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold ParvX86.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc ParvX86.ps0) with 0xae310 in Hms. change (SR.ps_regs ParvX86.ps0) with (map (fun i => (i, nth i ParvX86.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells ParvX86.ps0) with ParvX86.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' ParvX86.regs0 ParvX86.regs_out0 72 KS_arvX86 KS_arvX86_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg ParvX86.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth ParvX86.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvX86.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParvX86.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg ParvX86.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParvX86.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module ParvX87 := BndP_Ea_046S8.LibSegEa_arvX87.
Definition KS_arvX87 : list nat := Eval vm_compute in (BG.kept_list 72 ParvX87.regs0 ParvX87.regs_out0).
Lemma KS_arvX87_ok : BG.kept_ok 72 ParvX87.regs0 ParvX87.regs_out0 KS_arvX87 = true. Proof. vm_compute. reflexivity. Qed.
Lemma arvX87_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 12) = Z_to_bv 64 99 -> getr R (reg 18) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 47%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 (V 37%nat) -> getr R (reg 23) = Z_to_bv 64 87 -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 47%nat) ->
  L5.img_clear M 65536 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6914048 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 128)) -> 6914048 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 128) + 128 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 128)) ->
  ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3aec M) (st fx' R' 0xae310 M')
        /\ (forall x, In x KS_arvX87 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 738448
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 6).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G12 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI6 K4 K5 pvzI7 K7 K8 K9 K10 K11 K12 K13 pvzI8 K15 K16 K17 K18 K19 K20.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K6l; move K6l before pvzI7; pose proof (proj2 pvzI7) as K6r; move K6r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K14l; move K14l before pvzI8; pose proof (proj2 pvzI8) as K14r; move K14r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 48%nat. }
  assert (HR: regs_ok E ParvX87.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParvX87.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParvX87.kn0).
  { unfold know_ok, ParvX87.kn0.
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
  pvz_hg ltac:(idtac; destruct (ParvX87.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParvX87.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold ParvX87.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc ParvX87.ps0) with 0xae310 in Hms. change (SR.ps_regs ParvX87.ps0) with (map (fun i => (i, nth i ParvX87.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells ParvX87.ps0) with ParvX87.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' ParvX87.regs0 ParvX87.regs_out0 72 KS_arvX87 KS_arvX87_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg ParvX87.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth ParvX87.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvX87.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParvX87.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg ParvX87.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParvX87.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module ParvX88 := BndP_Ea_046S8.LibSegEa_arvX88.
Definition KS_arvX88 : list nat := Eval vm_compute in (BG.kept_list 72 ParvX88.regs0 ParvX88.regs_out0).
Lemma KS_arvX88_ok : BG.kept_ok 72 ParvX88.regs0 ParvX88.regs_out0 KS_arvX88 = true. Proof. vm_compute. reflexivity. Qed.
Lemma arvX88_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 12) = Z_to_bv 64 99 -> getr R (reg 18) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 47%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 (V 37%nat) -> getr R (reg 23) = Z_to_bv 64 88 -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 47%nat) ->
  L5.img_clear M 65536 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6914048 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 128)) -> 6914048 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 128) + 128 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 128)) ->
  ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3aec M) (st fx' R' 0xae310 M')
        /\ (forall x, In x KS_arvX88 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 738448
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 6).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G12 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI6 K4 K5 pvzI7 K7 K8 K9 K10 K11 K12 K13 pvzI8 K15 K16 K17 K18 K19 K20.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K6l; move K6l before pvzI7; pose proof (proj2 pvzI7) as K6r; move K6r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K14l; move K14l before pvzI8; pose proof (proj2 pvzI8) as K14r; move K14r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 48%nat. }
  assert (HR: regs_ok E ParvX88.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParvX88.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParvX88.kn0).
  { unfold know_ok, ParvX88.kn0.
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
  pvz_hg ltac:(idtac; destruct (ParvX88.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParvX88.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold ParvX88.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc ParvX88.ps0) with 0xae310 in Hms. change (SR.ps_regs ParvX88.ps0) with (map (fun i => (i, nth i ParvX88.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells ParvX88.ps0) with ParvX88.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' ParvX88.regs0 ParvX88.regs_out0 72 KS_arvX88 KS_arvX88_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg ParvX88.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth ParvX88.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvX88.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParvX88.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg ParvX88.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParvX88.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module ParvX89 := BndP_Ea_046S8.LibSegEa_arvX89.
Definition KS_arvX89 : list nat := Eval vm_compute in (BG.kept_list 72 ParvX89.regs0 ParvX89.regs_out0).
Lemma KS_arvX89_ok : BG.kept_ok 72 ParvX89.regs0 ParvX89.regs_out0 KS_arvX89 = true. Proof. vm_compute. reflexivity. Qed.
Lemma arvX89_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 12) = Z_to_bv 64 99 -> getr R (reg 18) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 47%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 (V 37%nat) -> getr R (reg 23) = Z_to_bv 64 89 -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 47%nat) ->
  L5.img_clear M 65536 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6914048 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 128)) -> 6914048 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 128) + 128 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 128)) ->
  ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3aec M) (st fx' R' 0xae310 M')
        /\ (forall x, In x KS_arvX89 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 738448
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 6).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G12 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI6 K4 K5 pvzI7 K7 K8 K9 K10 K11 K12 K13 pvzI8 K15 K16 K17 K18 K19 K20.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K6l; move K6l before pvzI7; pose proof (proj2 pvzI7) as K6r; move K6r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K14l; move K14l before pvzI8; pose proof (proj2 pvzI8) as K14r; move K14r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 48%nat. }
  assert (HR: regs_ok E ParvX89.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParvX89.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParvX89.kn0).
  { unfold know_ok, ParvX89.kn0.
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
  pvz_hg ltac:(idtac; destruct (ParvX89.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParvX89.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold ParvX89.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc ParvX89.ps0) with 0xae310 in Hms. change (SR.ps_regs ParvX89.ps0) with (map (fun i => (i, nth i ParvX89.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells ParvX89.ps0) with ParvX89.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' ParvX89.regs0 ParvX89.regs_out0 72 KS_arvX89 KS_arvX89_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg ParvX89.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth ParvX89.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvX89.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParvX89.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg ParvX89.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParvX89.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module ParvY0 := BndP_Ea_046S8.LibSegEa_arvY0.
Definition KS_arvY0 : list nat := Eval vm_compute in (BG.kept_list 72 ParvY0.regs0 ParvY0.regs_out0).
Lemma KS_arvY0_ok : BG.kept_ok 72 ParvY0.regs0 ParvY0.regs_out0 KS_arvY0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma arvY0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 12) = Z_to_bv 64 99 -> getr R (reg 18) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 47%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 (V 37%nat) -> getr R (reg 23) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 47%nat) ->
  L5.img_clear M 65536 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6914048 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 128)) -> 6914048 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 128) + 128 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 128)) ->
  ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) -> 0 <= (V 33%nat) <= 66 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3aec M) (st fx' R' 0xae310 M')
        /\ (forall x, In x KS_arvY0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 738448
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 6).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G12 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 pvzI9 K15 K16 K17 K18 K19 K20 pvzI10.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV47l; move HV47l before pvzI6; pose proof (proj2 pvzI6) as HV47r; move HV47r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K21l; move K21l before pvzI10; pose proof (proj2 pvzI10) as K21r; move K21r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 48%nat. }
  assert (HR: regs_ok E ParvY0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParvY0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParvY0.kn0).
  { unfold know_ok, ParvY0.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (ParvY0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParvY0.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold ParvY0.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc ParvY0.ps0) with 0xae310 in Hms. change (SR.ps_regs ParvY0.ps0) with (map (fun i => (i, nth i ParvY0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells ParvY0.ps0) with ParvY0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' ParvY0.regs0 ParvY0.regs_out0 72 KS_arvY0 KS_arvY0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg ParvY0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth ParvY0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvY0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParvY0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg ParvY0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParvY0.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module ParvY92 := BndP_Ea_046S8.LibSegEa_arvY92.
Definition KS_arvY92 : list nat := Eval vm_compute in (BG.kept_list 72 ParvY92.regs0 ParvY92.regs_out0).
Lemma KS_arvY92_ok : BG.kept_ok 72 ParvY92.regs0 ParvY92.regs_out0 KS_arvY92 = true. Proof. vm_compute. reflexivity. Qed.
Lemma arvY92_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 12) = Z_to_bv 64 99 -> getr R (reg 18) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 47%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 (V 37%nat) -> getr R (reg 23) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 47%nat) ->
  L5.img_clear M 65536 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6914048 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 128)) -> 6914048 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 128) + 128 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 128)) ->
  ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) -> 92 <= (V 33%nat) <= 99 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3aec M) (st fx' R' 0xae310 M')
        /\ (forall x, In x KS_arvY92 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 738448
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 6).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G12 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 pvzI9 K15 K16 K17 K18 K19 K20 pvzI10.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV47l; move HV47l before pvzI6; pose proof (proj2 pvzI6) as HV47r; move HV47r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K21l; move K21l before pvzI10; pose proof (proj2 pvzI10) as K21r; move K21r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 48%nat. }
  assert (HR: regs_ok E ParvY92.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParvY92.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParvY92.kn0).
  { unfold know_ok, ParvY92.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (ParvY92.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParvY92.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold ParvY92.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc ParvY92.ps0) with 0xae310 in Hms. change (SR.ps_regs ParvY92.ps0) with (map (fun i => (i, nth i ParvY92.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells ParvY92.ps0) with ParvY92.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' ParvY92.regs0 ParvY92.regs_out0 72 KS_arvY92 KS_arvY92_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg ParvY92.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth ParvY92.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvY92.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParvY92.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg ParvY92.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParvY92.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module ParvY101 := BndP_Ea_046S8.LibSegEa_arvY101.
Definition KS_arvY101 : list nat := Eval vm_compute in (BG.kept_list 72 ParvY101.regs0 ParvY101.regs_out0).
Lemma KS_arvY101_ok : BG.kept_ok 72 ParvY101.regs0 ParvY101.regs_out0 KS_arvY101 = true. Proof. vm_compute. reflexivity. Qed.
Lemma arvY101_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 12) = Z_to_bv 64 99 -> getr R (reg 18) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 47%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 (V 37%nat) -> getr R (reg 23) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 47%nat) ->
  L5.img_clear M 65536 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6914048 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 128)) -> 6914048 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 128) + 128 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 128)) ->
  ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) -> 101 <= (V 33%nat) <= 104 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3aec M) (st fx' R' 0xae310 M')
        /\ (forall x, In x KS_arvY101 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 738448
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 6).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G12 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 pvzI9 K15 K16 K17 K18 K19 K20 pvzI10.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV47l; move HV47l before pvzI6; pose proof (proj2 pvzI6) as HV47r; move HV47r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K21l; move K21l before pvzI10; pose proof (proj2 pvzI10) as K21r; move K21r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 48%nat. }
  assert (HR: regs_ok E ParvY101.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParvY101.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParvY101.kn0).
  { unfold know_ok, ParvY101.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (ParvY101.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParvY101.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold ParvY101.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc ParvY101.ps0) with 0xae310 in Hms. change (SR.ps_regs ParvY101.ps0) with (map (fun i => (i, nth i ParvY101.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells ParvY101.ps0) with ParvY101.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' ParvY101.regs0 ParvY101.regs_out0 72 KS_arvY101 KS_arvY101_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg ParvY101.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth ParvY101.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvY101.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParvY101.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg ParvY101.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParvY101.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module ParvY106 := BndP_Ea_046S8.LibSegEa_arvY106.
Definition KS_arvY106 : list nat := Eval vm_compute in (BG.kept_list 72 ParvY106.regs0 ParvY106.regs_out0).
Lemma KS_arvY106_ok : BG.kept_ok 72 ParvY106.regs0 ParvY106.regs_out0 KS_arvY106 = true. Proof. vm_compute. reflexivity. Qed.
Lemma arvY106_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 12) = Z_to_bv 64 99 -> getr R (reg 18) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 47%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 (V 37%nat) -> getr R (reg 23) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 47%nat) ->
  L5.img_clear M 65536 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6914048 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 128)) -> 6914048 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 128) + 128 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 128)) ->
  ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) -> 106 <= (V 33%nat) <= 107 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3aec M) (st fx' R' 0xae310 M')
        /\ (forall x, In x KS_arvY106 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 738448
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 6).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G12 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 pvzI9 K15 K16 K17 K18 K19 K20 pvzI10.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV47l; move HV47l before pvzI6; pose proof (proj2 pvzI6) as HV47r; move HV47r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K21l; move K21l before pvzI10; pose proof (proj2 pvzI10) as K21r; move K21r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 48%nat. }
  assert (HR: regs_ok E ParvY106.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParvY106.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParvY106.kn0).
  { unfold know_ok, ParvY106.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (ParvY106.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParvY106.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold ParvY106.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc ParvY106.ps0) with 0xae310 in Hms. change (SR.ps_regs ParvY106.ps0) with (map (fun i => (i, nth i ParvY106.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells ParvY106.ps0) with ParvY106.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' ParvY106.regs0 ParvY106.regs_out0 72 KS_arvY106 KS_arvY106_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg ParvY106.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth ParvY106.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvY106.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParvY106.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg ParvY106.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParvY106.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module ParvY109 := BndP_Ea_046S8.LibSegEa_arvY109.
Definition KS_arvY109 : list nat := Eval vm_compute in (BG.kept_list 72 ParvY109.regs0 ParvY109.regs_out0).
Lemma KS_arvY109_ok : BG.kept_ok 72 ParvY109.regs0 ParvY109.regs_out0 KS_arvY109 = true. Proof. vm_compute. reflexivity. Qed.
Lemma arvY109_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 12) = Z_to_bv 64 99 -> getr R (reg 18) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 47%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 (V 37%nat) -> getr R (reg 23) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 47%nat) ->
  L5.img_clear M 65536 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6914048 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 128)) -> 6914048 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 128) + 128 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 128)) ->
  ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) -> 109 <= (V 33%nat) <= 122 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3aec M) (st fx' R' 0xae310 M')
        /\ (forall x, In x KS_arvY109 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 738448
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 6).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G12 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 pvzI9 K15 K16 K17 K18 K19 K20 pvzI10.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV47l; move HV47l before pvzI6; pose proof (proj2 pvzI6) as HV47r; move HV47r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K21l; move K21l before pvzI10; pose proof (proj2 pvzI10) as K21r; move K21r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 48%nat. }
  assert (HR: regs_ok E ParvY109.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParvY109.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParvY109.kn0).
  { unfold know_ok, ParvY109.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (ParvY109.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParvY109.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold ParvY109.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc ParvY109.ps0) with 0xae310 in Hms. change (SR.ps_regs ParvY109.ps0) with (map (fun i => (i, nth i ParvY109.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells ParvY109.ps0) with ParvY109.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' ParvY109.regs0 ParvY109.regs_out0 72 KS_arvY109 KS_arvY109_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg ParvY109.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth ParvY109.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvY109.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParvY109.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg ParvY109.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParvY109.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module ParvY124 := BndP_Ea_046S8.LibSegEa_arvY124.
Definition KS_arvY124 : list nat := Eval vm_compute in (BG.kept_list 72 ParvY124.regs0 ParvY124.regs_out0).
Lemma KS_arvY124_ok : BG.kept_ok 72 ParvY124.regs0 ParvY124.regs_out0 KS_arvY124 = true. Proof. vm_compute. reflexivity. Qed.
Lemma arvY124_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 12) = Z_to_bv 64 99 -> getr R (reg 18) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 47%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 (V 37%nat) -> getr R (reg 23) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 47%nat) ->
  L5.img_clear M 65536 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6914048 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 128)) -> 6914048 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 128) + 128 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 128)) ->
  ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) -> 124 <= (V 33%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3aec M) (st fx' R' 0xae310 M')
        /\ (forall x, In x KS_arvY124 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 738448
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 6).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G12 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 pvzI9 K15 K16 K17 K18 K19 K20 pvzI10.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV47l; move HV47l before pvzI6; pose proof (proj2 pvzI6) as HV47r; move HV47r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K21l; move K21l before pvzI10; pose proof (proj2 pvzI10) as K21r; move K21r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 48%nat. }
  assert (HR: regs_ok E ParvY124.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParvY124.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParvY124.kn0).
  { unfold know_ok, ParvY124.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (ParvY124.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParvY124.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold ParvY124.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc ParvY124.ps0) with 0xae310 in Hms. change (SR.ps_regs ParvY124.ps0) with (map (fun i => (i, nth i ParvY124.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells ParvY124.ps0) with ParvY124.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' ParvY124.regs0 ParvY124.regs_out0 72 KS_arvY124 KS_arvY124_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg ParvY124.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth ParvY124.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParvY124.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParvY124.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg ParvY124.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParvY124.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

End PEARVP2.
