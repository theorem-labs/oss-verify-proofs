(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BigLinkZA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Es0PlanKit AsanPlanCore
     BigLinkBase BigLinkGlue L5Defs L5Kn.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.seg Require BndP_Es_002S8 BndP_Es_003S8 BndP_Es_004S8 BndP_Es_005S8.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PESENDP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).

Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5K.zpoly Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
  intros A Pz. rewrite (BG.word_of_unsigned (edenot E e) (z mod BL.MM) (L5K.zpoly_sound E Vz e z A Pz)).
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
  first [ rewrite Z.mod_small; [ first [reflexivity | k; lia] | k; L5K.zrange_tac ]
        | symmetry; eapply (Z.mod_unique_pos _ _ (-1)); k; unfold BL.MM; lia
        | symmetry; eapply (Z.mod_unique_pos _ _ 1); k; unfold BL.MM; lia ].

Local Ltac pvz_hg tac := lazymatch goal with |- ?G0 => let PG := fresh "PGoal" in set (PG := G0); tac; subst PG end.
Local Ltac pvz_fold B k := lazymatch B with | ?A2 /\ ?B2 => pvz_fold B2 ltac:(fun T2 => let T := fresh "pvzT" in pose (T := A2 /\ T2); k T) | _ => k B end.
Local Ltac pvz_linconj := lazymatch goal with |- ?A /\ ?B => pvz_fold B ltac:(fun T => change_no_check (A /\ T)) | _ => idtac end.
Local Ltac pvz_unfold ZA := lazymatch type of ZA with forall j, _ = ?f j => tryif is_var f then unfold f else idtac | _ => idtac end.
Tactic Notation "evalEk" constr(ZA) tactic(k) :=
  L5K.norm_expr; eapply L5K.zpoly_val; [ apply (L5K.zagree_all _ _ _ ZA) | cbn [L5K.zpoly]; pvz_unfold ZA; reflexivity | solve_modk k ].
Tactic Notation "evalEk'" constr(ZA) constr(AG) tactic(k) :=
  L5K.norm_expr; eapply L5K.zpoly_val;
  [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity] | cbn [L5K.zpoly]; pvz_unfold ZA; reflexivity | solve_modk k ].

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
          end; exact H ].

Local Ltac den_tac := first [reflexivity | lia | idtac].

Local Ltac apc_norm :=
  repeat match goal with
  | |- context [APC.eadd ?a ?b] => let t := eval vm_compute in (APC.eadd a b) in change (APC.eadd a b) with t
  | |- context [APC.esub ?a ?b] => let t := eval vm_compute in (APC.esub a b) in change (APC.esub a b) with t
  | |- context [APC.escale ?c ?e] => let t := eval vm_compute in (APC.escale c e) in change (APC.escale c e) with t
  | |- context [APC.eaddz ?a ?z] => let t := eval vm_compute in (APC.eaddz a z) in change (APC.eaddz a z) with t
  end.
Local Ltac slotP ZA :=
  first [ assumption | reflexivity
        | (etransitivity; [eassumption|]; symmetry; eapply word_of_zpoly; [apply (L5K.zagree_all _ _ _ ZA) | cbn [L5K.zpoly]; pvz_unfold ZA; f_equal; clear; lia]) ].

Local Ltac wordP' ZA AG :=
  eapply word_of_zpoly; [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity]
                        | cbn [L5K.zpoly]; pvz_unfold ZA; f_equal; clear; lia ].

Module PencEACe10 := BndP_Es_002S8.LibSegEs_encEACe10.
Definition KS_encEACe10 : list nat := Eval vm_compute in (BG.kept_list 60 PencEACe10.regs0 PencEACe10.regs_out0).
Lemma KS_encEACe10_ok : BG.kept_ok 60 PencEACe10.regs0 PencEACe10.regs_out0 KS_encEACe10 = true. Proof. vm_compute. reflexivity. Qed.
Lemma encEACe10_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 24) (V 33%nat) -> 4096 <= (V 33%nat) <= 140737488355328 ->
  aligned (V 33%nat) 8 -> L5.u32_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 48) (V 36%nat) -> 1 <= (V 36%nat) <= 1025 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 32) ((V 33%nat) + 24) ->
  L5.u32_at RSEGS M (V 33%nat) 0 -> L5.u64_at RSEGS M ((V 33%nat) + 8) (V 38%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 16) (V 38%nat) -> 0 <= (V 38%nat) <= 16777216 ->
  ((V 33%nat) + 24 <= ((V 2%nat) - 48) \/ ((V 2%nat) - 48) + 48 <= (V 33%nat)) -> ((V 33%nat) + 24 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= (V 33%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> ~ (((bv_unsigned (getr R (reg 10))) + 32) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= i < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> ~ (((bv_unsigned (getr R (reg 10))) + 32) <= i < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x357c4 M) (st fx' R' 0x35870 M')
        /\ (forall x, In x KS_encEACe10 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 38%nat)
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 32) (V 33%nat)
        /\ L5.u32_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 48) ((V 36%nat) - 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 pvzI6 K1 K2 pvzI7 K4 K5 K6 K7 pvzI8 K9 K10 pvzI9 K12 K13 pvzI10 K15 K16 K17 K18 pvzI11 K20 K21.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV41l; move HV41l before pvzI5; pose proof (proj2 pvzI5) as HV41r; move HV41r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K8l; move K8l before pvzI8; pose proof (proj2 pvzI8) as K8r; move K8r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K11l; move K11l before pvzI9; pose proof (proj2 pvzI9) as K11r; move K11r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K14l; move K14l before pvzI10; pose proof (proj2 pvzI10) as K14r; move K14r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K19l; move K19l before pvzI11; pose proof (proj2 pvzI11) as K19r; move K19r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_41 := V 41%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 41%nat => Z_to_bv 64 vz_41 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 36%nat => vz_36 | 38%nat => vz_38 | 41%nat => vz_41 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E PencEACe10.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PencEACe10.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PencEACe10.kn0).
  { unfold know_ok, PencEACe10.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K20) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K20) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K20) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K20; lia | clear - HV2l HV2r K0l K0r K6 K20; lia | clear - HV2l HV2r K0l K0r K6 K20; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K3l K3r K6 K21) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K3l K3r K6 K21) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K3l K3r K6 K21) | evalEk ZA ltac:(clear) | clear - K3l K3r K6 K21; lia | clear - K3l K3r K6 K21; lia | clear - K3l K3r K6 K21; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K21) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K21) | evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear - K3l K3r K6 K21; lia | clear - K3l K3r K6 K21; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K21) | evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K20 K21) | clear - K3l K3r K6 K21; lia | clear - K3l K3r K6 K21; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K20 K21) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K20 K21) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - K3l K3r K6 K21) | evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | clear - K3l K3r K6 K21; lia | clear - K3l K3r K6 K21; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K21) | evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K20 K21) | clear - K3l K3r K6 K21; lia | clear - K3l K3r K6 K21; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K20 K21) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K11l K11r K20 K21; lia | clear - HV33l HV33r K11l K11r K20 K21; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K20 K21) | evalEk ZA ltac:(clear - HV38l HV38r K19l K19r) | clear - HV33l HV33r K11l K11r K20 K21; lia | clear - HV33l HV33r K11l K11r K20 K21; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K20 K21) | evalEk ZA ltac:(clear - HV38l HV38r K19l K19r) | clear - HV33l HV33r K11l K11r K20 K21; lia | clear - HV33l HV33r K11l K11r K20 K21; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K20 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K20) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K20 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K21) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PencEACe10.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PencEACe10.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> ~ (((bv_unsigned (getr R (reg 10))) + 32) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PencEACe10.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K20) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K20 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K6 K21) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K6 K21 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K6 K21) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K6 K21 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PencEACe10.ps0) with 0x35870 in Hms. change (SR.ps_regs PencEACe10.ps0) with (map (fun i => (i, nth i PencEACe10.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PencEACe10.ps0) with PencEACe10.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PencEACe10.regs0 PencEACe10.regs_out0 60 KS_encEACe10 KS_encEACe10_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PencEACe10.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PencEACe10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEACe10.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PencEACe10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEACe10.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PencEACe10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEACe10.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PencEACe10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEACe10.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PencEACe10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K21) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K11l K11r K20 K21) | clear; lia]. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K21) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K14l K14r) | clear; lia].
Qed.

Module PencEACe12 := BndP_Es_002S8.LibSegEs_encEACe12.
Definition KS_encEACe12 : list nat := Eval vm_compute in (BG.kept_list 60 PencEACe12.regs0 PencEACe12.regs_out0).
Lemma KS_encEACe12_ok : BG.kept_ok 60 PencEACe12.regs0 PencEACe12.regs_out0 KS_encEACe12 = true. Proof. vm_compute. reflexivity. Qed.
Lemma encEACe12_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 24) (V 33%nat) -> 4096 <= (V 33%nat) <= 140737488355328 ->
  aligned (V 33%nat) 8 -> L5.u32_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 48) (V 36%nat) -> 1 <= (V 36%nat) <= 1025 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 32) ((V 33%nat) + 24) ->
  L5.u32_at RSEGS M (V 33%nat) 2 -> L5.u64_at RSEGS M ((V 33%nat) + 8) (V 38%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 16) (V 38%nat) -> 0 <= (V 38%nat) <= 16777216 ->
  ((V 33%nat) + 24 <= ((V 2%nat) - 48) \/ ((V 2%nat) - 48) + 48 <= (V 33%nat)) -> ((V 33%nat) + 24 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= (V 33%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> ~ (((bv_unsigned (getr R (reg 10))) + 32) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= i < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> ~ (((bv_unsigned (getr R (reg 10))) + 32) <= i < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x357c4 M) (st fx' R' 0x35870 M')
        /\ (forall x, In x KS_encEACe12 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 38%nat)
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 32) (V 33%nat)
        /\ L5.u32_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 48) ((V 36%nat) - 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 pvzI6 K1 K2 pvzI7 K4 K5 K6 K7 pvzI8 K9 K10 pvzI9 K12 K13 pvzI10 K15 K16 K17 K18 pvzI11 K20 K21.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV41l; move HV41l before pvzI5; pose proof (proj2 pvzI5) as HV41r; move HV41r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K8l; move K8l before pvzI8; pose proof (proj2 pvzI8) as K8r; move K8r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K11l; move K11l before pvzI9; pose proof (proj2 pvzI9) as K11r; move K11r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K14l; move K14l before pvzI10; pose proof (proj2 pvzI10) as K14r; move K14r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K19l; move K19l before pvzI11; pose proof (proj2 pvzI11) as K19r; move K19r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_41 := V 41%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 41%nat => Z_to_bv 64 vz_41 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 36%nat => vz_36 | 38%nat => vz_38 | 41%nat => vz_41 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E PencEACe12.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PencEACe12.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PencEACe12.kn0).
  { unfold know_ok, PencEACe12.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K20) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K20) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K20) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K20; lia | clear - HV2l HV2r K0l K0r K6 K20; lia | clear - HV2l HV2r K0l K0r K6 K20; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K3l K3r K6 K21) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K3l K3r K6 K21) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K3l K3r K6 K21) | evalEk ZA ltac:(clear) | clear - K3l K3r K6 K21; lia | clear - K3l K3r K6 K21; lia | clear - K3l K3r K6 K21; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K21) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K21) | evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear - K3l K3r K6 K21; lia | clear - K3l K3r K6 K21; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K21) | evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K20 K21) | clear - K3l K3r K6 K21; lia | clear - K3l K3r K6 K21; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K20 K21) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K20 K21) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - K3l K3r K6 K21) | evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | clear - K3l K3r K6 K21; lia | clear - K3l K3r K6 K21; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K21) | evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K20 K21) | clear - K3l K3r K6 K21; lia | clear - K3l K3r K6 K21; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K20 K21) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K11l K11r K20 K21; lia | clear - HV33l HV33r K11l K11r K20 K21; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K20 K21) | evalEk ZA ltac:(clear - HV38l HV38r K19l K19r) | clear - HV33l HV33r K11l K11r K20 K21; lia | clear - HV33l HV33r K11l K11r K20 K21; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K20 K21) | evalEk ZA ltac:(clear - HV38l HV38r K19l K19r) | clear - HV33l HV33r K11l K11r K20 K21; lia | clear - HV33l HV33r K11l K11r K20 K21; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K20 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K20) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K20 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K21) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PencEACe12.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PencEACe12.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> ~ (((bv_unsigned (getr R (reg 10))) + 32) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PencEACe12.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K20) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K20 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K6 K21) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K6 K21 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K6 K21) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K6 K21 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PencEACe12.ps0) with 0x35870 in Hms. change (SR.ps_regs PencEACe12.ps0) with (map (fun i => (i, nth i PencEACe12.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PencEACe12.ps0) with PencEACe12.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PencEACe12.regs0 PencEACe12.regs_out0 60 KS_encEACe12 KS_encEACe12_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PencEACe12.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PencEACe12.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEACe12.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PencEACe12.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEACe12.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PencEACe12.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEACe12.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PencEACe12.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEACe12.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PencEACe12.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K21) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K11l K11r K20 K21) | clear; lia]. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K21) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K14l K14r) | clear; lia].
Qed.

Module PencEACe20 := BndP_Es_003S8.LibSegEs_encEACe20.
Definition KS_encEACe20 : list nat := Eval vm_compute in (BG.kept_list 60 PencEACe20.regs0 PencEACe20.regs_out0).
Lemma KS_encEACe20_ok : BG.kept_ok 60 PencEACe20.regs0 PencEACe20.regs_out0 KS_encEACe20 = true. Proof. vm_compute. reflexivity. Qed.
Lemma encEACe20_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 24) (V 33%nat) -> 4096 <= (V 33%nat) <= 140737488355328 ->
  aligned (V 33%nat) 8 -> L5.u32_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 48) (V 36%nat) -> 1 <= (V 36%nat) <= 1025 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 32) (V 34%nat) ->
  4144 <= (V 34%nat) <= 140737488355328 -> aligned (V 34%nat) 8 -> 48 <= ((V 34%nat) - (V 33%nat)) <= 100000 -> L5.u32_at RSEGS M ((V 34%nat) - 24) 0 ->
  L5.u64_at RSEGS M ((V 34%nat) - 16) (V 38%nat) -> L5.u64_at RSEGS M ((V 34%nat) - 8) (V 38%nat) -> L5.u64_at RSEGS M ((V 34%nat) - 32) (V 42%nat) -> 0 <= (V 42%nat) <= 18446744073709551614 ->
  0 <= (V 38%nat) <= 16777216 -> L5.writable RSEGS M ((V 34%nat) - 48) 48 -> (((V 34%nat) - 48) + 48 <= ((V 2%nat) - 48) \/ ((V 2%nat) - 48) + 48 <= ((V 34%nat) - 48)) -> (((V 34%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 34%nat) - 48)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> ~ (((bv_unsigned (getr R (reg 10))) + 32) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> ~ (((V 34%nat) - 32) <= bv_unsigned a < ((V 34%nat) - 32) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= i < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> ~ (((bv_unsigned (getr R (reg 10))) + 32) <= i < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> ~ (((V 34%nat) - 32) <= i < ((V 34%nat) - 32) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x357c4 M) (st fx' R' 0x35870 M')
        /\ (forall x, In x KS_encEACe20 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 42%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 34%nat) - 24)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 34%nat) - 32) ((V 42%nat) + 1)
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 32) ((V 34%nat) - 24)
        /\ L5.u32_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 48) ((V 36%nat) - 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 pvzI8 K1 K2 pvzI9 K4 K5 K6 K7 pvzI10 K9 K10 pvzI11 K12 K13 pvzI12 K15 pvzI13 K17 pvzI14 K19 K20 K21 K22 pvzI15 pvzI16 K25 K26 K27.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV41l; move HV41l before pvzI6; pose proof (proj2 pvzI6) as HV41r; move HV41r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV42l; move HV42l before pvzI7; pose proof (proj2 pvzI7) as HV42r; move HV42r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K8l; move K8l before pvzI10; pose proof (proj2 pvzI10) as K8r; move K8r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K11l; move K11l before pvzI11; pose proof (proj2 pvzI11) as K11r; move K11r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K14l; move K14l before pvzI12; pose proof (proj2 pvzI12) as K14r; move K14r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K16l; move K16l before pvzI13; pose proof (proj2 pvzI13) as K16r; move K16r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K18l; move K18l before pvzI14; pose proof (proj2 pvzI14) as K18r; move K18r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K23l; move K23l before pvzI15; pose proof (proj2 pvzI15) as K23r; move K23r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K24l; move K24l before pvzI16; pose proof (proj2 pvzI16) as K24r; move K24r before pvzI16; clear pvzI16.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 38%nat => vz_38 | 41%nat => vz_41 | 42%nat => vz_42 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 43%nat. }
  assert (HR: regs_ok E PencEACe20.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PencEACe20.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PencEACe20.kn0).
  { unfold know_ok, PencEACe20.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K26) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K26) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K26) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K26; lia | clear - HV2l HV2r K0l K0r K6 K26; lia | clear - HV2l HV2r K0l K0r K6 K26; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K3l K3r K6 K27) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K3l K3r K6 K27) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K3l K3r K6 K27) | evalEk ZA ltac:(clear) | clear - K3l K3r K6 K27; lia | clear - K3l K3r K6 K27; lia | clear - K3l K3r K6 K27; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K27) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K27) | evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear - K3l K3r K6 K27; lia | clear - K3l K3r K6 K27; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K27) | evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear - K3l K3r K6 K27; lia | clear - K3l K3r K6 K27; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - K3l K3r K6 K27) | evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | clear - K3l K3r K6 K27; lia | clear - K3l K3r K6 K27; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K27) | evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | clear - K3l K3r K6 K27; lia | clear - K3l K3r K6 K27; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r HV34l HV34r K16l K16r K26 K27) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K16l K16r K18l K18r K26 K27; lia | clear - HV34l HV34r K16l K16r K18l K18r K26 K27; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | evalEk ZA ltac:(clear - HV38l HV38r K24l K24r) | clear - HV34l HV34r K16l K16r K18l K18r K26 K27; lia | clear - HV34l HV34r K16l K16r K18l K18r K26 K27; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | evalEk ZA ltac:(clear - HV38l HV38r K24l K24r) | clear - HV34l HV34r K16l K16r K18l K18r K26 K27; lia | clear - HV34l HV34r K16l K16r K18l K18r K26 K27; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | evalEk ZA ltac:(clear - HV42l HV42r K23l K23r) | clear - HV34l HV34r K16l K16r K18l K18r K26 K27; lia | clear - HV34l HV34r K16l K16r K18l K18r K26 K27; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K24l K24r) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K16l K16r K18l K18r K26 K27; lia | clear - HV34l HV34r K16l K16r K18l K18r K26 K27; lia | clear - HV34l HV34r K16l K16r K18l K18r K26 K27; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K26) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K27) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PencEACe20.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PencEACe20.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> ~ (((bv_unsigned (getr R (reg 10))) + 32) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> ~ ((vz_34 - 32) <= bv_unsigned a < (vz_34 - 32) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PencEACe20.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K26 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K6 K27) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K6 K27 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K6 K27) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K6 K27 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | evalEk' ZA Hag ltac:(clear) | clear - HV34l HV34r K16l K16r K18l K18r K26 K27 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PencEACe20.ps0) with 0x35870 in Hms. change (SR.ps_regs PencEACe20.ps0) with (map (fun i => (i, nth i PencEACe20.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PencEACe20.ps0) with PencEACe20.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PencEACe20.regs0 PencEACe20.regs_out0 60 KS_encEACe20 KS_encEACe20_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PencEACe20.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PencEACe20.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEACe20.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PencEACe20.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEACe20.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PencEACe20.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEACe20.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PencEACe20.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEACe20.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PencEACe20.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | evalEk' ZA Hag ltac:(clear - HV42l HV42r K23l K23r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K27) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | clear; lia]. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K27) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K14l K14r) | clear; lia].
Qed.

Module PencEACe20w := BndP_Es_003S8.LibSegEs_encEACe20w.
Definition KS_encEACe20w : list nat := Eval vm_compute in (BG.kept_list 60 PencEACe20w.regs0 PencEACe20w.regs_out0).
Lemma KS_encEACe20w_ok : BG.kept_ok 60 PencEACe20w.regs0 PencEACe20w.regs_out0 KS_encEACe20w = true. Proof. vm_compute. reflexivity. Qed.
Lemma encEACe20w_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 24) (V 33%nat) -> 4096 <= (V 33%nat) <= 140737488355328 ->
  aligned (V 33%nat) 8 -> L5.u32_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 48) (V 36%nat) -> 1 <= (V 36%nat) <= 1025 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 32) (V 34%nat) ->
  4144 <= (V 34%nat) <= 140737488355328 -> aligned (V 34%nat) 8 -> 48 <= ((V 34%nat) - (V 33%nat)) <= 100000 -> L5.u32_at RSEGS M ((V 34%nat) - 24) 0 ->
  L5.u64_at RSEGS M ((V 34%nat) - 16) (V 38%nat) -> L5.u64_at RSEGS M ((V 34%nat) - 8) (V 38%nat) -> L5.u64_at RSEGS M ((V 34%nat) - 32) 18446744073709551615 -> 0 <= (V 38%nat) <= 16777216 ->
  L5.writable RSEGS M ((V 34%nat) - 48) 48 -> (((V 34%nat) - 48) + 48 <= ((V 2%nat) - 48) \/ ((V 2%nat) - 48) + 48 <= ((V 34%nat) - 48)) -> (((V 34%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 34%nat) - 48)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> ~ (((bv_unsigned (getr R (reg 10))) + 32) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> ~ (((V 34%nat) - 32) <= bv_unsigned a < ((V 34%nat) - 32) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= i < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> ~ (((bv_unsigned (getr R (reg 10))) + 32) <= i < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> ~ (((V 34%nat) - 32) <= i < ((V 34%nat) - 32) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x357c4 M) (st fx' R' 0x35870 M')
        /\ (forall x, In x KS_encEACe20w -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 34%nat) - 24)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 34%nat) - 32) 0
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 32) ((V 34%nat) - 24)
        /\ L5.u32_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 48) ((V 36%nat) - 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 pvzI7 K1 K2 pvzI8 K4 K5 K6 K7 pvzI9 K9 K10 pvzI10 K12 K13 pvzI11 K15 pvzI12 K17 pvzI13 K19 K20 K21 K22 pvzI14 K24 K25 K26.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV41l; move HV41l before pvzI6; pose proof (proj2 pvzI6) as HV41r; move HV41r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K8l; move K8l before pvzI9; pose proof (proj2 pvzI9) as K8r; move K8r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K11l; move K11l before pvzI10; pose proof (proj2 pvzI10) as K11r; move K11r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K14l; move K14l before pvzI11; pose proof (proj2 pvzI11) as K14r; move K14r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K16l; move K16l before pvzI12; pose proof (proj2 pvzI12) as K16r; move K16r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K18l; move K18l before pvzI13; pose proof (proj2 pvzI13) as K18r; move K18r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K23l; move K23l before pvzI14; pose proof (proj2 pvzI14) as K23r; move K23r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_41 := V 41%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 41%nat => Z_to_bv 64 vz_41 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 38%nat => vz_38 | 41%nat => vz_41 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E PencEACe20w.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PencEACe20w.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PencEACe20w.kn0).
  { unfold know_ok, PencEACe20w.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K25) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K25) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K25) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K25; lia | clear - HV2l HV2r K0l K0r K6 K25; lia | clear - HV2l HV2r K0l K0r K6 K25; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K3l K3r K6 K26) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K3l K3r K6 K26) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K3l K3r K6 K26) | evalEk ZA ltac:(clear) | clear - K3l K3r K6 K26; lia | clear - K3l K3r K6 K26; lia | clear - K3l K3r K6 K26; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K25) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K26) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K26) | evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear - K3l K3r K6 K26; lia | clear - K3l K3r K6 K26; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K26) | evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear - K3l K3r K6 K26; lia | clear - K3l K3r K6 K26; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - K3l K3r K6 K26) | evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | clear - K3l K3r K6 K26; lia | clear - K3l K3r K6 K26; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K26) | evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | clear - K3l K3r K6 K26; lia | clear - K3l K3r K6 K26; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r HV34l HV34r K16l K16r K25 K26) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K16l K16r K18l K18r K25 K26; lia | clear - HV34l HV34r K16l K16r K18l K18r K25 K26; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | evalEk ZA ltac:(clear - HV38l HV38r K23l K23r) | clear - HV34l HV34r K16l K16r K18l K18r K25 K26; lia | clear - HV34l HV34r K16l K16r K18l K18r K25 K26; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | evalEk ZA ltac:(clear - HV38l HV38r K23l K23r) | clear - HV34l HV34r K16l K16r K18l K18r K25 K26; lia | clear - HV34l HV34r K16l K16r K18l K18r K25 K26; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K16l K16r K18l K18r K25 K26; lia | clear - HV34l HV34r K16l K16r K18l K18r K25 K26; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K16l K16r K18l K18r K25 K26; lia | clear - HV34l HV34r K16l K16r K18l K18r K25 K26; lia | clear - HV34l HV34r K16l K16r K18l K18r K25 K26; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K25) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K26) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PencEACe20w.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PencEACe20w.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> ~ (((bv_unsigned (getr R (reg 10))) + 32) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> ~ ((vz_34 - 32) <= bv_unsigned a < (vz_34 - 32) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PencEACe20w.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K25) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K25 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K6 K26) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K6 K26 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K6 K26) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K6 K26 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV34l HV34r K16l K16r K18l K18r K25 K26 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PencEACe20w.ps0) with 0x35870 in Hms. change (SR.ps_regs PencEACe20w.ps0) with (map (fun i => (i, nth i PencEACe20w.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PencEACe20w.ps0) with PencEACe20w.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PencEACe20w.regs0 PencEACe20w.regs_out0 60 KS_encEACe20w KS_encEACe20w_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PencEACe20w.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PencEACe20w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEACe20w.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PencEACe20w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEACe20w.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PencEACe20w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEACe20w.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PencEACe20w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEACe20w.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PencEACe20w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K26) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | clear; lia]. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K26) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K14l K14r) | clear; lia].
Qed.

Module PencEACe22 := BndP_Es_003S8.LibSegEs_encEACe22.
Definition KS_encEACe22 : list nat := Eval vm_compute in (BG.kept_list 60 PencEACe22.regs0 PencEACe22.regs_out0).
Lemma KS_encEACe22_ok : BG.kept_ok 60 PencEACe22.regs0 PencEACe22.regs_out0 KS_encEACe22 = true. Proof. vm_compute. reflexivity. Qed.
Lemma encEACe22_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 24) (V 33%nat) -> 4096 <= (V 33%nat) <= 140737488355328 ->
  aligned (V 33%nat) 8 -> L5.u32_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 48) (V 36%nat) -> 1 <= (V 36%nat) <= 1025 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 32) (V 34%nat) ->
  4144 <= (V 34%nat) <= 140737488355328 -> aligned (V 34%nat) 8 -> 48 <= ((V 34%nat) - (V 33%nat)) <= 100000 -> L5.u32_at RSEGS M ((V 34%nat) - 24) 2 ->
  L5.u64_at RSEGS M ((V 34%nat) - 16) (V 38%nat) -> L5.u64_at RSEGS M ((V 34%nat) - 8) (V 38%nat) -> L5.u64_at RSEGS M ((V 34%nat) - 32) (V 42%nat) -> 0 <= (V 42%nat) <= 18446744073709551614 ->
  0 <= (V 38%nat) <= 16777216 -> L5.writable RSEGS M ((V 34%nat) - 48) 48 -> (((V 34%nat) - 48) + 48 <= ((V 2%nat) - 48) \/ ((V 2%nat) - 48) + 48 <= ((V 34%nat) - 48)) -> (((V 34%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 34%nat) - 48)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> ~ (((bv_unsigned (getr R (reg 10))) + 32) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> ~ (((V 34%nat) - 32) <= bv_unsigned a < ((V 34%nat) - 32) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= i < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> ~ (((bv_unsigned (getr R (reg 10))) + 32) <= i < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> ~ (((V 34%nat) - 32) <= i < ((V 34%nat) - 32) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x357c4 M) (st fx' R' 0x35870 M')
        /\ (forall x, In x KS_encEACe22 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 42%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 34%nat) - 24)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 34%nat) - 32) ((V 42%nat) + 1)
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 32) ((V 34%nat) - 24)
        /\ L5.u32_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 48) ((V 36%nat) - 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 pvzI8 K1 K2 pvzI9 K4 K5 K6 K7 pvzI10 K9 K10 pvzI11 K12 K13 pvzI12 K15 pvzI13 K17 pvzI14 K19 K20 K21 K22 pvzI15 pvzI16 K25 K26 K27.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV41l; move HV41l before pvzI6; pose proof (proj2 pvzI6) as HV41r; move HV41r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV42l; move HV42l before pvzI7; pose proof (proj2 pvzI7) as HV42r; move HV42r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K8l; move K8l before pvzI10; pose proof (proj2 pvzI10) as K8r; move K8r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K11l; move K11l before pvzI11; pose proof (proj2 pvzI11) as K11r; move K11r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K14l; move K14l before pvzI12; pose proof (proj2 pvzI12) as K14r; move K14r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K16l; move K16l before pvzI13; pose proof (proj2 pvzI13) as K16r; move K16r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K18l; move K18l before pvzI14; pose proof (proj2 pvzI14) as K18r; move K18r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K23l; move K23l before pvzI15; pose proof (proj2 pvzI15) as K23r; move K23r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K24l; move K24l before pvzI16; pose proof (proj2 pvzI16) as K24r; move K24r before pvzI16; clear pvzI16.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 38%nat => vz_38 | 41%nat => vz_41 | 42%nat => vz_42 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 43%nat. }
  assert (HR: regs_ok E PencEACe22.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PencEACe22.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PencEACe22.kn0).
  { unfold know_ok, PencEACe22.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K26) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K26) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K26) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K26; lia | clear - HV2l HV2r K0l K0r K6 K26; lia | clear - HV2l HV2r K0l K0r K6 K26; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K3l K3r K6 K27) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K3l K3r K6 K27) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K3l K3r K6 K27) | evalEk ZA ltac:(clear) | clear - K3l K3r K6 K27; lia | clear - K3l K3r K6 K27; lia | clear - K3l K3r K6 K27; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K27) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K27) | evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear - K3l K3r K6 K27; lia | clear - K3l K3r K6 K27; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K27) | evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear - K3l K3r K6 K27; lia | clear - K3l K3r K6 K27; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - K3l K3r K6 K27) | evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | clear - K3l K3r K6 K27; lia | clear - K3l K3r K6 K27; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K27) | evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | clear - K3l K3r K6 K27; lia | clear - K3l K3r K6 K27; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r HV34l HV34r K16l K16r K26 K27) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K16l K16r K18l K18r K26 K27; lia | clear - HV34l HV34r K16l K16r K18l K18r K26 K27; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | evalEk ZA ltac:(clear - HV38l HV38r K24l K24r) | clear - HV34l HV34r K16l K16r K18l K18r K26 K27; lia | clear - HV34l HV34r K16l K16r K18l K18r K26 K27; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | evalEk ZA ltac:(clear - HV38l HV38r K24l K24r) | clear - HV34l HV34r K16l K16r K18l K18r K26 K27; lia | clear - HV34l HV34r K16l K16r K18l K18r K26 K27; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | evalEk ZA ltac:(clear - HV42l HV42r K23l K23r) | clear - HV34l HV34r K16l K16r K18l K18r K26 K27; lia | clear - HV34l HV34r K16l K16r K18l K18r K26 K27; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K24l K24r) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K16l K16r K18l K18r K26 K27; lia | clear - HV34l HV34r K16l K16r K18l K18r K26 K27; lia | clear - HV34l HV34r K16l K16r K18l K18r K26 K27; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K26) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K27) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PencEACe22.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PencEACe22.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> ~ (((bv_unsigned (getr R (reg 10))) + 32) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> ~ ((vz_34 - 32) <= bv_unsigned a < (vz_34 - 32) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PencEACe22.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K26 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K6 K27) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K6 K27 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K6 K27) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K6 K27 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | evalEk' ZA Hag ltac:(clear) | clear - HV34l HV34r K16l K16r K18l K18r K26 K27 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PencEACe22.ps0) with 0x35870 in Hms. change (SR.ps_regs PencEACe22.ps0) with (map (fun i => (i, nth i PencEACe22.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PencEACe22.ps0) with PencEACe22.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PencEACe22.regs0 PencEACe22.regs_out0 60 KS_encEACe22 KS_encEACe22_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PencEACe22.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PencEACe22.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEACe22.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PencEACe22.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEACe22.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PencEACe22.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEACe22.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PencEACe22.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEACe22.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PencEACe22.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | evalEk' ZA Hag ltac:(clear - HV42l HV42r K23l K23r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K27) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | clear; lia]. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K27) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K14l K14r) | clear; lia].
Qed.

Module PencEACe22w := BndP_Es_003S8.LibSegEs_encEACe22w.
Definition KS_encEACe22w : list nat := Eval vm_compute in (BG.kept_list 60 PencEACe22w.regs0 PencEACe22w.regs_out0).
Lemma KS_encEACe22w_ok : BG.kept_ok 60 PencEACe22w.regs0 PencEACe22w.regs_out0 KS_encEACe22w = true. Proof. vm_compute. reflexivity. Qed.
Lemma encEACe22w_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 24) (V 33%nat) -> 4096 <= (V 33%nat) <= 140737488355328 ->
  aligned (V 33%nat) 8 -> L5.u32_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 48) (V 36%nat) -> 1 <= (V 36%nat) <= 1025 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 32) (V 34%nat) ->
  4144 <= (V 34%nat) <= 140737488355328 -> aligned (V 34%nat) 8 -> 48 <= ((V 34%nat) - (V 33%nat)) <= 100000 -> L5.u32_at RSEGS M ((V 34%nat) - 24) 2 ->
  L5.u64_at RSEGS M ((V 34%nat) - 16) (V 38%nat) -> L5.u64_at RSEGS M ((V 34%nat) - 8) (V 38%nat) -> L5.u64_at RSEGS M ((V 34%nat) - 32) 18446744073709551615 -> 0 <= (V 38%nat) <= 16777216 ->
  L5.writable RSEGS M ((V 34%nat) - 48) 48 -> (((V 34%nat) - 48) + 48 <= ((V 2%nat) - 48) \/ ((V 2%nat) - 48) + 48 <= ((V 34%nat) - 48)) -> (((V 34%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 34%nat) - 48)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> ~ (((bv_unsigned (getr R (reg 10))) + 32) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> ~ (((V 34%nat) - 32) <= bv_unsigned a < ((V 34%nat) - 32) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= i < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> ~ (((bv_unsigned (getr R (reg 10))) + 32) <= i < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> ~ (((V 34%nat) - 32) <= i < ((V 34%nat) - 32) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x357c4 M) (st fx' R' 0x35870 M')
        /\ (forall x, In x KS_encEACe22w -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 34%nat) - 24)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 34%nat) - 32) 0
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 32) ((V 34%nat) - 24)
        /\ L5.u32_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 48) ((V 36%nat) - 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 pvzI7 K1 K2 pvzI8 K4 K5 K6 K7 pvzI9 K9 K10 pvzI10 K12 K13 pvzI11 K15 pvzI12 K17 pvzI13 K19 K20 K21 K22 pvzI14 K24 K25 K26.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV41l; move HV41l before pvzI6; pose proof (proj2 pvzI6) as HV41r; move HV41r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K8l; move K8l before pvzI9; pose proof (proj2 pvzI9) as K8r; move K8r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K11l; move K11l before pvzI10; pose proof (proj2 pvzI10) as K11r; move K11r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K14l; move K14l before pvzI11; pose proof (proj2 pvzI11) as K14r; move K14r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K16l; move K16l before pvzI12; pose proof (proj2 pvzI12) as K16r; move K16r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K18l; move K18l before pvzI13; pose proof (proj2 pvzI13) as K18r; move K18r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K23l; move K23l before pvzI14; pose proof (proj2 pvzI14) as K23r; move K23r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_41 := V 41%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 41%nat => Z_to_bv 64 vz_41 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 38%nat => vz_38 | 41%nat => vz_41 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E PencEACe22w.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PencEACe22w.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PencEACe22w.kn0).
  { unfold know_ok, PencEACe22w.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K25) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K25) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K25) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K25; lia | clear - HV2l HV2r K0l K0r K6 K25; lia | clear - HV2l HV2r K0l K0r K6 K25; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K3l K3r K6 K26) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K3l K3r K6 K26) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K3l K3r K6 K26) | evalEk ZA ltac:(clear) | clear - K3l K3r K6 K26; lia | clear - K3l K3r K6 K26; lia | clear - K3l K3r K6 K26; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K25) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K26) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K26) | evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear - K3l K3r K6 K26; lia | clear - K3l K3r K6 K26; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K26) | evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear - K3l K3r K6 K26; lia | clear - K3l K3r K6 K26; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - K3l K3r K6 K26) | evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | clear - K3l K3r K6 K26; lia | clear - K3l K3r K6 K26; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K26) | evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | clear - K3l K3r K6 K26; lia | clear - K3l K3r K6 K26; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r HV34l HV34r K16l K16r K25 K26) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K16l K16r K18l K18r K25 K26; lia | clear - HV34l HV34r K16l K16r K18l K18r K25 K26; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | evalEk ZA ltac:(clear - HV38l HV38r K23l K23r) | clear - HV34l HV34r K16l K16r K18l K18r K25 K26; lia | clear - HV34l HV34r K16l K16r K18l K18r K25 K26; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | evalEk ZA ltac:(clear - HV38l HV38r K23l K23r) | clear - HV34l HV34r K16l K16r K18l K18r K25 K26; lia | clear - HV34l HV34r K16l K16r K18l K18r K25 K26; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K16l K16r K18l K18r K25 K26; lia | clear - HV34l HV34r K16l K16r K18l K18r K25 K26; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K16l K16r K18l K18r K25 K26; lia | clear - HV34l HV34r K16l K16r K18l K18r K25 K26; lia | clear - HV34l HV34r K16l K16r K18l K18r K25 K26; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K25) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K26) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PencEACe22w.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PencEACe22w.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> ~ (((bv_unsigned (getr R (reg 10))) + 32) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> ~ ((vz_34 - 32) <= bv_unsigned a < (vz_34 - 32) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PencEACe22w.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K25) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K25 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K6 K26) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K6 K26 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K6 K26) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K6 K26 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV34l HV34r K16l K16r K18l K18r K25 K26 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PencEACe22w.ps0) with 0x35870 in Hms. change (SR.ps_regs PencEACe22w.ps0) with (map (fun i => (i, nth i PencEACe22w.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PencEACe22w.ps0) with PencEACe22w.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PencEACe22w.regs0 PencEACe22w.regs_out0 60 KS_encEACe22w KS_encEACe22w_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PencEACe22w.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PencEACe22w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEACe22w.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PencEACe22w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEACe22w.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PencEACe22w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEACe22w.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PencEACe22w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEACe22w.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PencEACe22w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K26) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | clear; lia]. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K26) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K14l K14r) | clear; lia].
Qed.

Module PencEACgt0 := BndP_Es_003S8.LibSegEs_encEACgt0.
Definition KS_encEACgt0 : list nat := Eval vm_compute in (BG.kept_list 60 PencEACgt0.regs0 PencEACgt0.regs_out0).
Lemma KS_encEACgt0_ok : BG.kept_ok 60 PencEACgt0.regs0 PencEACgt0.regs_out0 KS_encEACgt0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma encEACgt0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 24) (V 33%nat) -> 4096 <= (V 33%nat) <= 140737488355328 ->
  aligned (V 33%nat) 8 -> L5.u32_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 48) (V 36%nat) -> 1 <= (V 36%nat) <= 1025 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 32) (V 34%nat) ->
  4120 <= (V 34%nat) <= 140737488355328 -> aligned (V 34%nat) 8 -> 24 <= ((V 34%nat) - (V 33%nat)) <= 100000 -> L5.u32_at RSEGS M ((V 34%nat) - 24) 0 ->
  L5.u64_at RSEGS M ((V 34%nat) - 16) (V 38%nat) -> 0 <= (V 38%nat) <= 16777216 -> (((V 34%nat) - 48) + 48 <= ((V 2%nat) - 48) \/ ((V 2%nat) - 48) + 48 <= ((V 34%nat) - 48)) -> (((V 34%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 34%nat) - 48)) ->
  L5.u64_at RSEGS M ((V 34%nat) - 8) ((V 38%nat) + (V 43%nat)) -> 1 <= (V 43%nat) <= 18446744073692774399 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= i < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x357c4 M) (st fx' R' 0x36f18 M')
        /\ (forall x, In x KS_encEACgt0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 219228
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 10) = getr R (reg 12)
        /\ getr R' (reg 11) = Z_to_bv 64 8
        /\ getr R' (reg 13) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 38%nat) + (V 43%nat))
        /\ L5.u32_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 48) ((V 36%nat) - 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 pvzI8 K1 K2 pvzI9 K4 K5 K6 K7 pvzI10 K9 K10 pvzI11 K12 K13 pvzI12 K15 pvzI13 K17 pvzI14 K19 K20 pvzI15 K22 K23 K24 pvzI16.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV41l; move HV41l before pvzI6; pose proof (proj2 pvzI6) as HV41r; move HV41r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV43l; move HV43l before pvzI7; pose proof (proj2 pvzI7) as HV43r; move HV43r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K8l; move K8l before pvzI10; pose proof (proj2 pvzI10) as K8r; move K8r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K11l; move K11l before pvzI11; pose proof (proj2 pvzI11) as K11r; move K11r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K14l; move K14l before pvzI12; pose proof (proj2 pvzI12) as K14r; move K14r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K16l; move K16l before pvzI13; pose proof (proj2 pvzI13) as K16r; move K16r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K18l; move K18l before pvzI14; pose proof (proj2 pvzI14) as K18r; move K18r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K21l; move K21l before pvzI15; pose proof (proj2 pvzI15) as K21r; move K21r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K25l; move K25l before pvzI16; pose proof (proj2 pvzI16) as K25r; move K25r before pvzI16; clear pvzI16.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_43 := V 43%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 41%nat => Z_to_bv 64 vz_41 | 43%nat => Z_to_bv 64 vz_43 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 38%nat => vz_38 | 41%nat => vz_41 | 43%nat => vz_43 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E PencEACgt0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PencEACgt0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PencEACgt0.kn0).
  { unfold know_ok, PencEACgt0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K22; lia | clear - HV2l HV2r K0l K0r K6 K22; lia | clear - HV2l HV2r K0l K0r K6 K22; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r HV34l HV34r K16l K16r K22 K23) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear - HV38l HV38r K21l K21r) | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear - HV38l HV38r K21l K21r HV43l HV43r K25l K25r) | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PencEACgt0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PencEACgt0.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PencEACgt0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K22 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K6 K23) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K6 K23 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PencEACgt0.ps0) with 0x36f18 in Hms. change (SR.ps_regs PencEACgt0.ps0) with (map (fun i => (i, nth i PencEACgt0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PencEACgt0.ps0) with PencEACgt0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PencEACgt0.regs0 PencEACgt0.regs_out0 60 KS_encEACgt0 KS_encEACgt0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PencEACgt0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PencEACgt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEACgt0.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PencEACgt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEACgt0.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PencEACgt0.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PencEACgt0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PencEACgt0.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PencEACgt0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PencEACgt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEACgt0.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PencEACgt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEACgt0.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PencEACgt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K23) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K14l K14r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PencEACgt2 := BndP_Es_003S8.LibSegEs_encEACgt2.
Definition KS_encEACgt2 : list nat := Eval vm_compute in (BG.kept_list 60 PencEACgt2.regs0 PencEACgt2.regs_out0).
Lemma KS_encEACgt2_ok : BG.kept_ok 60 PencEACgt2.regs0 PencEACgt2.regs_out0 KS_encEACgt2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma encEACgt2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 24) (V 33%nat) -> 4096 <= (V 33%nat) <= 140737488355328 ->
  aligned (V 33%nat) 8 -> L5.u32_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 48) (V 36%nat) -> 1 <= (V 36%nat) <= 1025 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 32) (V 34%nat) ->
  4120 <= (V 34%nat) <= 140737488355328 -> aligned (V 34%nat) 8 -> 24 <= ((V 34%nat) - (V 33%nat)) <= 100000 -> L5.u32_at RSEGS M ((V 34%nat) - 24) 2 ->
  L5.u64_at RSEGS M ((V 34%nat) - 16) (V 38%nat) -> 0 <= (V 38%nat) <= 16777216 -> (((V 34%nat) - 48) + 48 <= ((V 2%nat) - 48) \/ ((V 2%nat) - 48) + 48 <= ((V 34%nat) - 48)) -> (((V 34%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 34%nat) - 48)) ->
  L5.u64_at RSEGS M ((V 34%nat) - 8) ((V 38%nat) + (V 43%nat)) -> 1 <= (V 43%nat) <= 18446744073692774399 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= i < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x357c4 M) (st fx' R' 0x36f18 M')
        /\ (forall x, In x KS_encEACgt2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 219228
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 10) = getr R (reg 12)
        /\ getr R' (reg 11) = Z_to_bv 64 8
        /\ getr R' (reg 13) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 38%nat) + (V 43%nat))
        /\ L5.u32_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 48) ((V 36%nat) - 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 pvzI8 K1 K2 pvzI9 K4 K5 K6 K7 pvzI10 K9 K10 pvzI11 K12 K13 pvzI12 K15 pvzI13 K17 pvzI14 K19 K20 pvzI15 K22 K23 K24 pvzI16.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV41l; move HV41l before pvzI6; pose proof (proj2 pvzI6) as HV41r; move HV41r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV43l; move HV43l before pvzI7; pose proof (proj2 pvzI7) as HV43r; move HV43r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K8l; move K8l before pvzI10; pose proof (proj2 pvzI10) as K8r; move K8r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K11l; move K11l before pvzI11; pose proof (proj2 pvzI11) as K11r; move K11r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K14l; move K14l before pvzI12; pose proof (proj2 pvzI12) as K14r; move K14r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K16l; move K16l before pvzI13; pose proof (proj2 pvzI13) as K16r; move K16r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K18l; move K18l before pvzI14; pose proof (proj2 pvzI14) as K18r; move K18r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K21l; move K21l before pvzI15; pose proof (proj2 pvzI15) as K21r; move K21r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K25l; move K25l before pvzI16; pose proof (proj2 pvzI16) as K25r; move K25r before pvzI16; clear pvzI16.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_43 := V 43%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 41%nat => Z_to_bv 64 vz_41 | 43%nat => Z_to_bv 64 vz_43 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 38%nat => vz_38 | 41%nat => vz_41 | 43%nat => vz_43 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E PencEACgt2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PencEACgt2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PencEACgt2.kn0).
  { unfold know_ok, PencEACgt2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K22; lia | clear - HV2l HV2r K0l K0r K6 K22; lia | clear - HV2l HV2r K0l K0r K6 K22; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r HV34l HV34r K16l K16r K22 K23) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear - HV38l HV38r K21l K21r) | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear - HV38l HV38r K21l K21r HV43l HV43r K25l K25r) | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PencEACgt2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PencEACgt2.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PencEACgt2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K22 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K6 K23) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K6 K23 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PencEACgt2.ps0) with 0x36f18 in Hms. change (SR.ps_regs PencEACgt2.ps0) with (map (fun i => (i, nth i PencEACgt2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PencEACgt2.ps0) with PencEACgt2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PencEACgt2.regs0 PencEACgt2.regs_out0 60 KS_encEACgt2 KS_encEACgt2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PencEACgt2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PencEACgt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEACgt2.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PencEACgt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEACgt2.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PencEACgt2.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PencEACgt2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PencEACgt2.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PencEACgt2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PencEACgt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEACgt2.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PencEACgt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEACgt2.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PencEACgt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K23) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K14l K14r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PencEACgth0 := BndP_Es_003S8.LibSegEs_encEACgth0.
Definition KS_encEACgth0 : list nat := Eval vm_compute in (BG.kept_list 60 PencEACgth0.regs0 PencEACgth0.regs_out0).
Lemma KS_encEACgth0_ok : BG.kept_ok 60 PencEACgth0.regs0 PencEACgth0.regs_out0 KS_encEACgth0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma encEACgth0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 24) (V 33%nat) -> 4096 <= (V 33%nat) <= 140737488355328 ->
  aligned (V 33%nat) 8 -> L5.u32_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 48) (V 36%nat) -> 1 <= (V 36%nat) <= 1025 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 32) (V 34%nat) ->
  4120 <= (V 34%nat) <= 140737488355328 -> aligned (V 34%nat) 8 -> 24 <= ((V 34%nat) - (V 33%nat)) <= 100000 -> L5.u32_at RSEGS M ((V 34%nat) - 24) 0 ->
  L5.u64_at RSEGS M ((V 34%nat) - 16) (V 38%nat) -> 0 <= (V 38%nat) <= 16777216 -> (((V 34%nat) - 48) + 48 <= ((V 2%nat) - 48) \/ ((V 2%nat) - 48) + 48 <= ((V 34%nat) - 48)) -> (((V 34%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 34%nat) - 48)) ->
  L5.u64_at RSEGS M ((V 34%nat) - 8) (V 39%nat) -> 18446744073692774400 <= (V 39%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= i < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x357c4 M) (st fx' R' 0x36f18 M')
        /\ (forall x, In x KS_encEACgth0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 219228
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 10) = getr R (reg 12)
        /\ getr R' (reg 11) = Z_to_bv 64 8
        /\ getr R' (reg 13) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 39%nat)
        /\ L5.u32_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 48) ((V 36%nat) - 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 pvzI8 K1 K2 pvzI9 K4 K5 K6 K7 pvzI10 K9 K10 pvzI11 K12 K13 pvzI12 K15 pvzI13 K17 pvzI14 K19 K20 pvzI15 K22 K23 K24 pvzI16.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV39l; move HV39l before pvzI6; pose proof (proj2 pvzI6) as HV39r; move HV39r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV41l; move HV41l before pvzI7; pose proof (proj2 pvzI7) as HV41r; move HV41r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K8l; move K8l before pvzI10; pose proof (proj2 pvzI10) as K8r; move K8r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K11l; move K11l before pvzI11; pose proof (proj2 pvzI11) as K11r; move K11r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K14l; move K14l before pvzI12; pose proof (proj2 pvzI12) as K14r; move K14r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K16l; move K16l before pvzI13; pose proof (proj2 pvzI13) as K16r; move K16r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K18l; move K18l before pvzI14; pose proof (proj2 pvzI14) as K18r; move K18r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K21l; move K21l before pvzI15; pose proof (proj2 pvzI15) as K21r; move K21r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K25l; move K25l before pvzI16; pose proof (proj2 pvzI16) as K25r; move K25r before pvzI16; clear pvzI16.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_41 := V 41%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 41%nat => Z_to_bv 64 vz_41 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 38%nat => vz_38 | 39%nat => vz_39 | 41%nat => vz_41 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E PencEACgth0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PencEACgth0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PencEACgth0.kn0).
  { unfold know_ok, PencEACgth0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K22; lia | clear - HV2l HV2r K0l K0r K6 K22; lia | clear - HV2l HV2r K0l K0r K6 K22; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r HV34l HV34r K16l K16r K22 K23) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear - HV38l HV38r K21l K21r) | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear - HV39l HV39r K25l K25r) | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PencEACgth0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PencEACgth0.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PencEACgth0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K22 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K6 K23) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K6 K23 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PencEACgth0.ps0) with 0x36f18 in Hms. change (SR.ps_regs PencEACgth0.ps0) with (map (fun i => (i, nth i PencEACgth0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PencEACgth0.ps0) with PencEACgth0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PencEACgth0.regs0 PencEACgth0.regs_out0 60 KS_encEACgth0 KS_encEACgth0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PencEACgth0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PencEACgth0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEACgth0.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PencEACgth0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEACgth0.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PencEACgth0.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PencEACgth0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PencEACgth0.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PencEACgth0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PencEACgth0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEACgth0.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PencEACgth0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEACgth0.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PencEACgth0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K23) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K14l K14r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PencEACgth2 := BndP_Es_003S8.LibSegEs_encEACgth2.
Definition KS_encEACgth2 : list nat := Eval vm_compute in (BG.kept_list 60 PencEACgth2.regs0 PencEACgth2.regs_out0).
Lemma KS_encEACgth2_ok : BG.kept_ok 60 PencEACgth2.regs0 PencEACgth2.regs_out0 KS_encEACgth2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma encEACgth2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 24) (V 33%nat) -> 4096 <= (V 33%nat) <= 140737488355328 ->
  aligned (V 33%nat) 8 -> L5.u32_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 48) (V 36%nat) -> 1 <= (V 36%nat) <= 1025 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 32) (V 34%nat) ->
  4120 <= (V 34%nat) <= 140737488355328 -> aligned (V 34%nat) 8 -> 24 <= ((V 34%nat) - (V 33%nat)) <= 100000 -> L5.u32_at RSEGS M ((V 34%nat) - 24) 2 ->
  L5.u64_at RSEGS M ((V 34%nat) - 16) (V 38%nat) -> 0 <= (V 38%nat) <= 16777216 -> (((V 34%nat) - 48) + 48 <= ((V 2%nat) - 48) \/ ((V 2%nat) - 48) + 48 <= ((V 34%nat) - 48)) -> (((V 34%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 34%nat) - 48)) ->
  L5.u64_at RSEGS M ((V 34%nat) - 8) (V 39%nat) -> 18446744073692774400 <= (V 39%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= i < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x357c4 M) (st fx' R' 0x36f18 M')
        /\ (forall x, In x KS_encEACgth2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 219228
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 10) = getr R (reg 12)
        /\ getr R' (reg 11) = Z_to_bv 64 8
        /\ getr R' (reg 13) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 39%nat)
        /\ L5.u32_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 48) ((V 36%nat) - 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 pvzI8 K1 K2 pvzI9 K4 K5 K6 K7 pvzI10 K9 K10 pvzI11 K12 K13 pvzI12 K15 pvzI13 K17 pvzI14 K19 K20 pvzI15 K22 K23 K24 pvzI16.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV39l; move HV39l before pvzI6; pose proof (proj2 pvzI6) as HV39r; move HV39r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV41l; move HV41l before pvzI7; pose proof (proj2 pvzI7) as HV41r; move HV41r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K8l; move K8l before pvzI10; pose proof (proj2 pvzI10) as K8r; move K8r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K11l; move K11l before pvzI11; pose proof (proj2 pvzI11) as K11r; move K11r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K14l; move K14l before pvzI12; pose proof (proj2 pvzI12) as K14r; move K14r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K16l; move K16l before pvzI13; pose proof (proj2 pvzI13) as K16r; move K16r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K18l; move K18l before pvzI14; pose proof (proj2 pvzI14) as K18r; move K18r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K21l; move K21l before pvzI15; pose proof (proj2 pvzI15) as K21r; move K21r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K25l; move K25l before pvzI16; pose proof (proj2 pvzI16) as K25r; move K25r before pvzI16; clear pvzI16.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_41 := V 41%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 41%nat => Z_to_bv 64 vz_41 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 38%nat => vz_38 | 39%nat => vz_39 | 41%nat => vz_41 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E PencEACgth2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PencEACgth2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PencEACgth2.kn0).
  { unfold know_ok, PencEACgth2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K22; lia | clear - HV2l HV2r K0l K0r K6 K22; lia | clear - HV2l HV2r K0l K0r K6 K22; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r HV34l HV34r K16l K16r K22 K23) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear - HV38l HV38r K21l K21r) | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear - HV39l HV39r K25l K25r) | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PencEACgth2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PencEACgth2.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PencEACgth2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K22 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K6 K23) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K6 K23 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PencEACgth2.ps0) with 0x36f18 in Hms. change (SR.ps_regs PencEACgth2.ps0) with (map (fun i => (i, nth i PencEACgth2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PencEACgth2.ps0) with PencEACgth2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PencEACgth2.regs0 PencEACgth2.regs_out0 60 KS_encEACgth2 KS_encEACgth2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PencEACgth2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PencEACgth2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEACgth2.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PencEACgth2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEACgth2.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PencEACgth2.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PencEACgth2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PencEACgth2.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PencEACgth2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PencEACgth2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEACgth2.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PencEACgth2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEACgth2.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PencEACgth2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K23) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K14l K14r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PencEAClt0 := BndP_Es_003S8.LibSegEs_encEAClt0.
Definition KS_encEAClt0 : list nat := Eval vm_compute in (BG.kept_list 60 PencEAClt0.regs0 PencEAClt0.regs_out0).
Lemma KS_encEAClt0_ok : BG.kept_ok 60 PencEAClt0.regs0 PencEAClt0.regs_out0 KS_encEAClt0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma encEAClt0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 24) (V 33%nat) -> 4096 <= (V 33%nat) <= 140737488355328 ->
  aligned (V 33%nat) 8 -> L5.u32_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 48) (V 36%nat) -> 1 <= (V 36%nat) <= 1025 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 32) (V 34%nat) ->
  4120 <= (V 34%nat) <= 140737488355328 -> aligned (V 34%nat) 8 -> 24 <= ((V 34%nat) - (V 33%nat)) <= 100000 -> L5.u32_at RSEGS M ((V 34%nat) - 24) 0 ->
  L5.u64_at RSEGS M ((V 34%nat) - 16) (V 38%nat) -> 0 <= (V 38%nat) <= 16777216 -> (((V 34%nat) - 48) + 48 <= ((V 2%nat) - 48) \/ ((V 2%nat) - 48) + 48 <= ((V 34%nat) - 48)) -> (((V 34%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 34%nat) - 48)) ->
  L5.u64_at RSEGS M ((V 34%nat) - 8) (V 39%nat) -> 0 <= (V 39%nat) <= 16777215 -> 1 <= ((V 38%nat) - (V 39%nat)) <= 16777216 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= i < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x357c4 M) (st fx' R' 0x36f18 M')
        /\ (forall x, In x KS_encEAClt0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 219228
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 10) = getr R (reg 12)
        /\ getr R' (reg 11) = Z_to_bv 64 9
        /\ getr R' (reg 13) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 39%nat)
        /\ L5.u32_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 48) ((V 36%nat) - 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 pvzI8 K1 K2 pvzI9 K4 K5 K6 K7 pvzI10 K9 K10 pvzI11 K12 K13 pvzI12 K15 pvzI13 K17 pvzI14 K19 K20 pvzI15 K22 K23 K24 pvzI16 pvzI17.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV39l; move HV39l before pvzI6; pose proof (proj2 pvzI6) as HV39r; move HV39r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV41l; move HV41l before pvzI7; pose proof (proj2 pvzI7) as HV41r; move HV41r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K8l; move K8l before pvzI10; pose proof (proj2 pvzI10) as K8r; move K8r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K11l; move K11l before pvzI11; pose proof (proj2 pvzI11) as K11r; move K11r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K14l; move K14l before pvzI12; pose proof (proj2 pvzI12) as K14r; move K14r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K16l; move K16l before pvzI13; pose proof (proj2 pvzI13) as K16r; move K16r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K18l; move K18l before pvzI14; pose proof (proj2 pvzI14) as K18r; move K18r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K21l; move K21l before pvzI15; pose proof (proj2 pvzI15) as K21r; move K21r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K25l; move K25l before pvzI16; pose proof (proj2 pvzI16) as K25r; move K25r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K26l; move K26l before pvzI17; pose proof (proj2 pvzI17) as K26r; move K26r before pvzI17; clear pvzI17.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_41 := V 41%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 41%nat => Z_to_bv 64 vz_41 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 38%nat => vz_38 | 39%nat => vz_39 | 41%nat => vz_41 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E PencEAClt0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PencEAClt0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PencEAClt0.kn0).
  { unfold know_ok, PencEAClt0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K22; lia | clear - HV2l HV2r K0l K0r K6 K22; lia | clear - HV2l HV2r K0l K0r K6 K22; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r HV34l HV34r K16l K16r K22 K23) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear - HV38l HV38r K21l K21r K26l K26r) | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K21l K21r K26l K26r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear - HV39l HV39r K25l K25r K26l K26r) | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K25l K25r K26l K26r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K21l K21r K26l K26r HV39l HV39r K25l K25r) | exact (conj K26l K26r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PencEAClt0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PencEAClt0.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PencEAClt0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K22 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K6 K23) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K6 K23 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PencEAClt0.ps0) with 0x36f18 in Hms. change (SR.ps_regs PencEAClt0.ps0) with (map (fun i => (i, nth i PencEAClt0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PencEAClt0.ps0) with PencEAClt0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PencEAClt0.regs0 PencEAClt0.regs_out0 60 KS_encEAClt0 KS_encEAClt0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PencEAClt0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PencEAClt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEAClt0.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PencEAClt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEAClt0.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PencEAClt0.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PencEAClt0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PencEAClt0.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PencEAClt0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PencEAClt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEAClt0.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PencEAClt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEAClt0.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PencEAClt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K23) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K14l K14r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PencEAClt2 := BndP_Es_003S8.LibSegEs_encEAClt2.
Definition KS_encEAClt2 : list nat := Eval vm_compute in (BG.kept_list 60 PencEAClt2.regs0 PencEAClt2.regs_out0).
Lemma KS_encEAClt2_ok : BG.kept_ok 60 PencEAClt2.regs0 PencEAClt2.regs_out0 KS_encEAClt2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma encEAClt2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 24) (V 33%nat) -> 4096 <= (V 33%nat) <= 140737488355328 ->
  aligned (V 33%nat) 8 -> L5.u32_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 48) (V 36%nat) -> 1 <= (V 36%nat) <= 1025 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 32) (V 34%nat) ->
  4120 <= (V 34%nat) <= 140737488355328 -> aligned (V 34%nat) 8 -> 24 <= ((V 34%nat) - (V 33%nat)) <= 100000 -> L5.u32_at RSEGS M ((V 34%nat) - 24) 2 ->
  L5.u64_at RSEGS M ((V 34%nat) - 16) (V 38%nat) -> 0 <= (V 38%nat) <= 16777216 -> (((V 34%nat) - 48) + 48 <= ((V 2%nat) - 48) \/ ((V 2%nat) - 48) + 48 <= ((V 34%nat) - 48)) -> (((V 34%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 34%nat) - 48)) ->
  L5.u64_at RSEGS M ((V 34%nat) - 8) (V 39%nat) -> 0 <= (V 39%nat) <= 16777215 -> 1 <= ((V 38%nat) - (V 39%nat)) <= 16777216 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= i < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x357c4 M) (st fx' R' 0x36f18 M')
        /\ (forall x, In x KS_encEAClt2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 219228
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 10) = getr R (reg 12)
        /\ getr R' (reg 11) = Z_to_bv 64 9
        /\ getr R' (reg 13) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 39%nat)
        /\ L5.u32_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 48) ((V 36%nat) - 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 pvzI8 K1 K2 pvzI9 K4 K5 K6 K7 pvzI10 K9 K10 pvzI11 K12 K13 pvzI12 K15 pvzI13 K17 pvzI14 K19 K20 pvzI15 K22 K23 K24 pvzI16 pvzI17.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV39l; move HV39l before pvzI6; pose proof (proj2 pvzI6) as HV39r; move HV39r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV41l; move HV41l before pvzI7; pose proof (proj2 pvzI7) as HV41r; move HV41r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K8l; move K8l before pvzI10; pose proof (proj2 pvzI10) as K8r; move K8r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K11l; move K11l before pvzI11; pose proof (proj2 pvzI11) as K11r; move K11r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K14l; move K14l before pvzI12; pose proof (proj2 pvzI12) as K14r; move K14r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K16l; move K16l before pvzI13; pose proof (proj2 pvzI13) as K16r; move K16r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K18l; move K18l before pvzI14; pose proof (proj2 pvzI14) as K18r; move K18r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K21l; move K21l before pvzI15; pose proof (proj2 pvzI15) as K21r; move K21r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K25l; move K25l before pvzI16; pose proof (proj2 pvzI16) as K25r; move K25r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K26l; move K26l before pvzI17; pose proof (proj2 pvzI17) as K26r; move K26r before pvzI17; clear pvzI17.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_41 := V 41%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 41%nat => Z_to_bv 64 vz_41 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 38%nat => vz_38 | 39%nat => vz_39 | 41%nat => vz_41 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E PencEAClt2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PencEAClt2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PencEAClt2.kn0).
  { unfold know_ok, PencEAClt2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K22; lia | clear - HV2l HV2r K0l K0r K6 K22; lia | clear - HV2l HV2r K0l K0r K6 K22; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r HV34l HV34r K16l K16r K22 K23) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear - HV38l HV38r K21l K21r K26l K26r) | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K21l K21r K26l K26r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear - HV39l HV39r K25l K25r K26l K26r) | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K25l K25r K26l K26r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K21l K21r K26l K26r HV39l HV39r K25l K25r) | exact (conj K26l K26r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PencEAClt2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PencEAClt2.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PencEAClt2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K22 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K6 K23) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K6 K23 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PencEAClt2.ps0) with 0x36f18 in Hms. change (SR.ps_regs PencEAClt2.ps0) with (map (fun i => (i, nth i PencEAClt2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PencEAClt2.ps0) with PencEAClt2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PencEAClt2.regs0 PencEAClt2.regs_out0 60 KS_encEAClt2 KS_encEAClt2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PencEAClt2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PencEAClt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEAClt2.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PencEAClt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEAClt2.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PencEAClt2.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PencEAClt2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PencEAClt2.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PencEAClt2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PencEAClt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEAClt2.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PencEAClt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEAClt2.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PencEAClt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K23) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K14l K14r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PencEAI1 := BndP_Es_003S8.LibSegEs_encEAI1.
Definition KS_encEAI1 : list nat := Eval vm_compute in (BG.kept_list 60 PencEAI1.regs0 PencEAI1.regs_out0).
Lemma KS_encEAI1_ok : BG.kept_ok 60 PencEAI1.regs0 PencEAI1.regs_out0 KS_encEAI1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma encEAI1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 24) (V 33%nat) -> 4096 <= (V 33%nat) <= 140737488355328 ->
  aligned (V 33%nat) 8 -> L5.u32_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 48) (V 36%nat) -> 1 <= (V 36%nat) <= 1025 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 32) (V 34%nat) ->
  4120 <= (V 34%nat) <= 140737488355328 -> aligned (V 34%nat) 8 -> 24 <= ((V 34%nat) - (V 33%nat)) <= 100000 -> L5.u32_at RSEGS M ((V 34%nat) - 24) 1 ->
  L5.u64_at RSEGS M ((V 34%nat) - 16) (V 38%nat) -> L5.u64_at RSEGS M ((V 34%nat) - 8) (V 39%nat) -> 0 <= (V 38%nat) <= 16777216 -> 0 <= (V 39%nat) <= 18446744073709551615 ->
  (((V 34%nat) - 48) + 48 <= ((V 2%nat) - 48) \/ ((V 2%nat) - 48) + 48 <= ((V 34%nat) - 48)) -> (((V 34%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 34%nat) - 48)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= i < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x357c4 M) (st fx' R' 0x372d8 M')
        /\ (forall x, In x KS_encEAI1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 219156
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 13) = Z_to_bv 64 1
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 48) 93
        /\ L5.u32_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 48) ((V 36%nat) - 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 pvzI8 K1 K2 pvzI9 K4 K5 K6 K7 pvzI10 K9 K10 pvzI11 K12 K13 pvzI12 K15 pvzI13 K17 pvzI14 K19 K20 K21 pvzI15 pvzI16 K24 K25.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV39l; move HV39l before pvzI6; pose proof (proj2 pvzI6) as HV39r; move HV39r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV41l; move HV41l before pvzI7; pose proof (proj2 pvzI7) as HV41r; move HV41r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K8l; move K8l before pvzI10; pose proof (proj2 pvzI10) as K8r; move K8r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K11l; move K11l before pvzI11; pose proof (proj2 pvzI11) as K11r; move K11r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K14l; move K14l before pvzI12; pose proof (proj2 pvzI12) as K14r; move K14r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K16l; move K16l before pvzI13; pose proof (proj2 pvzI13) as K16r; move K16r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K18l; move K18l before pvzI14; pose proof (proj2 pvzI14) as K18r; move K18r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K22l; move K22l before pvzI15; pose proof (proj2 pvzI15) as K22r; move K22r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K23l; move K23l before pvzI16; pose proof (proj2 pvzI16) as K23r; move K23r before pvzI16; clear pvzI16.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_41 := V 41%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 41%nat => Z_to_bv 64 vz_41 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 38%nat => vz_38 | 39%nat => vz_39 | 41%nat => vz_41 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E PencEAI1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PencEAI1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PencEAI1.kn0).
  { unfold know_ok, PencEAI1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K24; lia | clear - HV2l HV2r K0l K0r K6 K24; lia | clear - HV2l HV2r K0l K0r K6 K24; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K3l K3r K6 K25) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K3l K3r K6 K25) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K3l K3r K6 K25) | evalEk ZA ltac:(clear) | clear - K3l K3r K6 K25; lia | clear - K3l K3r K6 K25; lia | clear - K3l K3r K6 K25; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K25) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K25) | evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear - K3l K3r K6 K25; lia | clear - K3l K3r K6 K25; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K25) | evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear - K3l K3r K6 K25; lia | clear - K3l K3r K6 K25; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - K3l K3r K6 K25) | evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | clear - K3l K3r K6 K25; lia | clear - K3l K3r K6 K25; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K25) | evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K24 K25) | clear - K3l K3r K6 K25; lia | clear - K3l K3r K6 K25; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K24 K25) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K24 K25) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r HV34l HV34r K16l K16r K24 K25) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K24 K25) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K16l K16r K18l K18r K24 K25; lia | clear - HV34l HV34r K16l K16r K18l K18r K24 K25; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K24 K25) | evalEk ZA ltac:(clear - HV38l HV38r K22l K22r) | clear - HV34l HV34r K16l K16r K18l K18r K24 K25; lia | clear - HV34l HV34r K16l K16r K18l K18r K24 K25; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K24 K25) | evalEk ZA ltac:(clear - HV39l HV39r K23l K23r) | clear - HV34l HV34r K16l K16r K18l K18r K24 K25; lia | clear - HV34l HV34r K16l K16r K18l K18r K24 K25; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K24 K25) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K24 K25) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K25) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PencEAI1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PencEAI1.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PencEAI1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K24 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K6 K25) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K6 K25 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PencEAI1.ps0) with 0x372d8 in Hms. change (SR.ps_regs PencEAI1.ps0) with (map (fun i => (i, nth i PencEAI1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PencEAI1.ps0) with PencEAI1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PencEAI1.regs0 PencEAI1.regs_out0 60 KS_encEAI1 KS_encEAI1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PencEAI1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PencEAI1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEAI1.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PencEAI1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEAI1.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PencEAI1.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PencEAI1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PencEAI1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEAI1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PencEAI1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEAI1.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PencEAI1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEAI1.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PencEAI1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K25) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K14l K14r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PencEAI3 := BndP_Es_003S8.LibSegEs_encEAI3.
Definition KS_encEAI3 : list nat := Eval vm_compute in (BG.kept_list 60 PencEAI3.regs0 PencEAI3.regs_out0).
Lemma KS_encEAI3_ok : BG.kept_ok 60 PencEAI3.regs0 PencEAI3.regs_out0 KS_encEAI3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma encEAI3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 24) (V 33%nat) -> 4096 <= (V 33%nat) <= 140737488355328 ->
  aligned (V 33%nat) 8 -> L5.u32_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 48) (V 36%nat) -> 1 <= (V 36%nat) <= 1025 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 32) (V 34%nat) ->
  4120 <= (V 34%nat) <= 140737488355328 -> aligned (V 34%nat) 8 -> 24 <= ((V 34%nat) - (V 33%nat)) <= 100000 -> L5.u32_at RSEGS M ((V 34%nat) - 24) 3 ->
  L5.u64_at RSEGS M ((V 34%nat) - 16) (V 38%nat) -> L5.u64_at RSEGS M ((V 34%nat) - 8) (V 39%nat) -> 0 <= (V 38%nat) <= 16777216 -> 0 <= (V 39%nat) <= 18446744073709551615 ->
  (((V 34%nat) - 48) + 48 <= ((V 2%nat) - 48) \/ ((V 2%nat) - 48) + 48 <= ((V 34%nat) - 48)) -> (((V 34%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 34%nat) - 48)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= i < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x357c4 M) (st fx' R' 0x372d8 M')
        /\ (forall x, In x KS_encEAI3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 219156
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 13) = Z_to_bv 64 1
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 48) 93
        /\ L5.u32_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 48) ((V 36%nat) - 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 pvzI8 K1 K2 pvzI9 K4 K5 K6 K7 pvzI10 K9 K10 pvzI11 K12 K13 pvzI12 K15 pvzI13 K17 pvzI14 K19 K20 K21 pvzI15 pvzI16 K24 K25.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV39l; move HV39l before pvzI6; pose proof (proj2 pvzI6) as HV39r; move HV39r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV41l; move HV41l before pvzI7; pose proof (proj2 pvzI7) as HV41r; move HV41r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K8l; move K8l before pvzI10; pose proof (proj2 pvzI10) as K8r; move K8r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K11l; move K11l before pvzI11; pose proof (proj2 pvzI11) as K11r; move K11r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K14l; move K14l before pvzI12; pose proof (proj2 pvzI12) as K14r; move K14r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K16l; move K16l before pvzI13; pose proof (proj2 pvzI13) as K16r; move K16r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K18l; move K18l before pvzI14; pose proof (proj2 pvzI14) as K18r; move K18r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K22l; move K22l before pvzI15; pose proof (proj2 pvzI15) as K22r; move K22r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K23l; move K23l before pvzI16; pose proof (proj2 pvzI16) as K23r; move K23r before pvzI16; clear pvzI16.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_41 := V 41%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 41%nat => Z_to_bv 64 vz_41 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 38%nat => vz_38 | 39%nat => vz_39 | 41%nat => vz_41 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E PencEAI3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PencEAI3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PencEAI3.kn0).
  { unfold know_ok, PencEAI3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K24; lia | clear - HV2l HV2r K0l K0r K6 K24; lia | clear - HV2l HV2r K0l K0r K6 K24; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K3l K3r K6 K25) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K3l K3r K6 K25) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K3l K3r K6 K25) | evalEk ZA ltac:(clear) | clear - K3l K3r K6 K25; lia | clear - K3l K3r K6 K25; lia | clear - K3l K3r K6 K25; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K25) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K25) | evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear - K3l K3r K6 K25; lia | clear - K3l K3r K6 K25; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K25) | evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear - K3l K3r K6 K25; lia | clear - K3l K3r K6 K25; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - K3l K3r K6 K25) | evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | clear - K3l K3r K6 K25; lia | clear - K3l K3r K6 K25; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K25) | evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K24 K25) | clear - K3l K3r K6 K25; lia | clear - K3l K3r K6 K25; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K24 K25) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K24 K25) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r HV34l HV34r K16l K16r K24 K25) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K24 K25) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K16l K16r K18l K18r K24 K25; lia | clear - HV34l HV34r K16l K16r K18l K18r K24 K25; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K24 K25) | evalEk ZA ltac:(clear - HV38l HV38r K22l K22r) | clear - HV34l HV34r K16l K16r K18l K18r K24 K25; lia | clear - HV34l HV34r K16l K16r K18l K18r K24 K25; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K24 K25) | evalEk ZA ltac:(clear - HV39l HV39r K23l K23r) | clear - HV34l HV34r K16l K16r K18l K18r K24 K25; lia | clear - HV34l HV34r K16l K16r K18l K18r K24 K25; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K24 K25) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K24 K25) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K25) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PencEAI3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PencEAI3.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PencEAI3.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K24 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K6 K25) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K6 K25 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PencEAI3.ps0) with 0x372d8 in Hms. change (SR.ps_regs PencEAI3.ps0) with (map (fun i => (i, nth i PencEAI3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PencEAI3.ps0) with PencEAI3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PencEAI3.regs0 PencEAI3.regs_out0 60 KS_encEAI3 KS_encEAI3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PencEAI3.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PencEAI3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEAI3.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PencEAI3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEAI3.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PencEAI3.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PencEAI3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PencEAI3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEAI3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PencEAI3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEAI3.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PencEAI3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEAI3.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PencEAI3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K25) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K14l K14r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PencEAJ1 := BndP_Es_003S8.LibSegEs_encEAJ1.
Definition KS_encEAJ1 : list nat := Eval vm_compute in (BG.kept_list 60 PencEAJ1.regs0 PencEAJ1.regs_out0).
Lemma KS_encEAJ1_ok : BG.kept_ok 60 PencEAJ1.regs0 PencEAJ1.regs_out0 KS_encEAJ1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma encEAJ1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 56 -> (((V 2%nat) - 48) + 48 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((V 10%nat) + 24) (V 33%nat) ->
  4096 <= (V 33%nat) <= 140737488355328 -> aligned (V 33%nat) 8 -> L5.u64_at RSEGS M ((V 10%nat) + 32) ((V 33%nat) + 24) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 10%nat) + 32) <= bv_unsigned a < ((V 10%nat) + 32) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 10%nat) + 32) <= i < ((V 10%nat) + 32) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x35814 M) (st fx' R' 0x35870 M')
        /\ (forall x, In x KS_encEAJ1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 10%nat) + 32) (V 33%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G10 pvzI8 K1 K2 pvzI9 K4 K5 K6 K7 pvzI10 K9 K10 K11 K12 K13.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV44l; move HV44l before pvzI4; pose proof (proj2 pvzI4) as HV44r; move HV44r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV45l; move HV45l before pvzI5; pose proof (proj2 pvzI5) as HV45r; move HV45r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV46l; move HV46l before pvzI6; pose proof (proj2 pvzI6) as HV46r; move HV46r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV55l; move HV55l before pvzI7; pose proof (proj2 pvzI7) as HV55r; move HV55r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K8l; move K8l before pvzI10; pose proof (proj2 pvzI10) as K8r; move K8r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_55 := V 55%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 33%nat => Z_to_bv 64 vz_33 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 55%nat => Z_to_bv 64 vz_55 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 33%nat => vz_33 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 55%nat => vz_55 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 56%nat. }
  assert (HR: regs_ok E PencEAJ1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PencEAJ1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PencEAJ1.kn0).
  { unfold know_ok, PencEAJ1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r) | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r) | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K13]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PencEAJ1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PencEAJ1.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_10 + 32) <= bv_unsigned a < (vz_10 + 32) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PencEAJ1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk' ZA Hag ltac:(clear) | clear - HV10l HV10r K3l K3r K6 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PencEAJ1.ps0) with 0x35870 in Hms. change (SR.ps_regs PencEAJ1.ps0) with (map (fun i => (i, nth i PencEAJ1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PencEAJ1.ps0) with PencEAJ1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PencEAJ1.regs0 PencEAJ1.regs_out0 60 KS_encEAJ1 KS_encEAJ1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PencEAJ1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PencEAJ1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEAJ1.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PencEAJ1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEAJ1.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PencEAJ1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEAJ1.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PencEAJ1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEAJ1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PencEAJ1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEAJ1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PencEAJ1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEAJ1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PencEAJ1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r) | clear; lia].
Qed.

Module PencEAJ2 := BndP_Es_003S8.LibSegEs_encEAJ2.
Definition KS_encEAJ2 : list nat := Eval vm_compute in (BG.kept_list 60 PencEAJ2.regs0 PencEAJ2.regs_out0).
Lemma KS_encEAJ2_ok : BG.kept_ok 60 PencEAJ2.regs0 PencEAJ2.regs_out0 KS_encEAJ2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma encEAJ2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 56 -> (((V 2%nat) - 48) + 48 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((V 10%nat) + 24) (V 33%nat) ->
  4096 <= (V 33%nat) <= 140737488355328 -> aligned (V 33%nat) 8 -> L5.u64_at RSEGS M ((V 10%nat) + 32) (V 34%nat) -> 4144 <= (V 34%nat) <= 140737488355328 ->
  aligned (V 34%nat) 8 -> 48 <= ((V 34%nat) - (V 33%nat)) <= 100000 -> L5.writable RSEGS M ((V 34%nat) - 48) 48 -> (((V 34%nat) - 48) + 48 <= ((V 2%nat) - 48) \/ ((V 2%nat) - 48) + 48 <= ((V 34%nat) - 48)) ->
  (((V 34%nat) - 48) + 48 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 34%nat) - 48)) -> L5.u64_at RSEGS M ((V 34%nat) - 32) (V 42%nat) -> 0 <= (V 42%nat) <= 18446744073709551614 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 10%nat) + 32) <= bv_unsigned a < ((V 10%nat) + 32) + 8) -> ~ (((V 34%nat) - 32) <= bv_unsigned a < ((V 34%nat) - 32) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 10%nat) + 32) <= i < ((V 10%nat) + 32) + 8) -> ~ (((V 34%nat) - 32) <= i < ((V 34%nat) - 32) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x35814 M) (st fx' R' 0x35870 M')
        /\ (forall x, In x KS_encEAJ2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 42%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 34%nat) - 24)
        /\ L5.u64_at RSEGS M' ((V 34%nat) - 32) ((V 42%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 10%nat) + 32) ((V 34%nat) - 24)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G8 G10 pvzI10 K1 K2 pvzI11 K4 K5 K6 K7 pvzI12 K9 K10 pvzI13 K12 pvzI14 K14 K15 K16 K17 pvzI15 K19 K20 K21.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV42l; move HV42l before pvzI5; pose proof (proj2 pvzI5) as HV42r; move HV42r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV44l; move HV44l before pvzI6; pose proof (proj2 pvzI6) as HV44r; move HV44r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV45l; move HV45l before pvzI7; pose proof (proj2 pvzI7) as HV45r; move HV45r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV46l; move HV46l before pvzI8; pose proof (proj2 pvzI8) as HV46r; move HV46r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV55l; move HV55l before pvzI9; pose proof (proj2 pvzI9) as HV55r; move HV55r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K0l; move K0l before pvzI10; pose proof (proj2 pvzI10) as K0r; move K0r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K3l; move K3l before pvzI11; pose proof (proj2 pvzI11) as K3r; move K3r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K8l; move K8l before pvzI12; pose proof (proj2 pvzI12) as K8r; move K8r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K11l; move K11l before pvzI13; pose proof (proj2 pvzI13) as K11r; move K11r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K13l; move K13l before pvzI14; pose proof (proj2 pvzI14) as K13r; move K13r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K18l; move K18l before pvzI15; pose proof (proj2 pvzI15) as K18r; move K18r before pvzI15; clear pvzI15.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_55 := V 55%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 42%nat => Z_to_bv 64 vz_42 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 55%nat => Z_to_bv 64 vz_55 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 33%nat => vz_33 | 34%nat => vz_34 | 42%nat => vz_42 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 55%nat => vz_55 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 56%nat. }
  assert (HR: regs_ok E PencEAJ2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PencEAJ2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PencEAJ2.kn0).
  { unfold know_ok, PencEAJ2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K15) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K15) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K15) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K15; lia | clear - HV2l HV2r K0l K0r K6 K15; lia | clear - HV2l HV2r K0l K0r K6 K15; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K16) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K16) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K16) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K3l K3r K6 K16; lia | clear - HV10l HV10r K3l K3r K6 K16; lia | clear - HV10l HV10r K3l K3r K6 K16; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K16) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K16) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K13l K13r) | clear - HV10l HV10r K3l K3r K6 K16; lia | clear - HV10l HV10r K3l K3r K6 K16; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K13l K13r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K13l K13r) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K16) | evalEk ZA ltac:(clear - HV34l HV34r K11l K11r K13l K13r K15 K16) | clear - HV10l HV10r K3l K3r K6 K16; lia | clear - HV10l HV10r K3l K3r K6 K16; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K11l K11r K13l K13r K15 K16) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K11l K11r K13l K13r K15 K16) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K13l K13r HV34l HV34r K11l K11r K15 K16) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV34l HV34r K11l K11r K13l K13r K15 K16) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K11l K11r K13l K13r K15 K16; lia | clear - HV34l HV34r K11l K11r K13l K13r K15 K16; lia | clear - HV34l HV34r K11l K11r K13l K13r K15 K16; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K11l K11r K13l K13r K15 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K15) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K11l K11r K13l K13r K15 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K16) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K11l K11r K13l K13r K15 K16) | evalEk ZA ltac:(clear - HV42l HV42r K18l K18r) | clear - HV34l HV34r K11l K11r K13l K13r K15 K16; lia | clear - HV34l HV34r K11l K11r K13l K13r K15 K16; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K18l K18r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K15) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K6 K15; lia | clear - HV2l HV2r K0l K0r K6 K15; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K15) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K6 K15; lia | clear - HV2l HV2r K0l K0r K6 K15; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K15) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K6 K15; lia | clear - HV2l HV2r K0l K0r K6 K15; lia | exactA K21]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PencEAJ2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PencEAJ2.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_10 + 32) <= bv_unsigned a < (vz_10 + 32) + 8) -> ~ ((vz_34 - 32) <= bv_unsigned a < (vz_34 - 32) + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PencEAJ2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6 K16) | evalEk' ZA Hag ltac:(clear) | clear - HV10l HV10r K3l K3r K6 K16 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV34l HV34r K11l K11r K13l K13r K15 K16) | evalEk' ZA Hag ltac:(clear) | clear - HV34l HV34r K11l K11r K13l K13r K15 K16 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PencEAJ2.ps0) with 0x35870 in Hms. change (SR.ps_regs PencEAJ2.ps0) with (map (fun i => (i, nth i PencEAJ2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PencEAJ2.ps0) with PencEAJ2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PencEAJ2.regs0 PencEAJ2.regs_out0 60 KS_encEAJ2 KS_encEAJ2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PencEAJ2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PencEAJ2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEAJ2.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PencEAJ2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEAJ2.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PencEAJ2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEAJ2.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PencEAJ2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEAJ2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PencEAJ2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEAJ2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PencEAJ2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEAJ2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PencEAJ2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV34l HV34r K11l K11r K13l K13r K15 K16) | evalEk' ZA Hag ltac:(clear - HV42l HV42r K18l K18r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6 K16) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K11l K11r K13l K13r K15 K16) | clear; lia].
Qed.

Module PencEAJ2w := BndP_Es_004S8.LibSegEs_encEAJ2w.
Definition KS_encEAJ2w : list nat := Eval vm_compute in (BG.kept_list 60 PencEAJ2w.regs0 PencEAJ2w.regs_out0).
Lemma KS_encEAJ2w_ok : BG.kept_ok 60 PencEAJ2w.regs0 PencEAJ2w.regs_out0 KS_encEAJ2w = true. Proof. vm_compute. reflexivity. Qed.
Lemma encEAJ2w_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 56 -> (((V 2%nat) - 48) + 48 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((V 10%nat) + 24) (V 33%nat) ->
  4096 <= (V 33%nat) <= 140737488355328 -> aligned (V 33%nat) 8 -> L5.u64_at RSEGS M ((V 10%nat) + 32) (V 34%nat) -> 4144 <= (V 34%nat) <= 140737488355328 ->
  aligned (V 34%nat) 8 -> 48 <= ((V 34%nat) - (V 33%nat)) <= 100000 -> L5.writable RSEGS M ((V 34%nat) - 48) 48 -> (((V 34%nat) - 48) + 48 <= ((V 2%nat) - 48) \/ ((V 2%nat) - 48) + 48 <= ((V 34%nat) - 48)) ->
  (((V 34%nat) - 48) + 48 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 34%nat) - 48)) -> L5.u64_at RSEGS M ((V 34%nat) - 32) 18446744073709551615 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 10%nat) + 32) <= bv_unsigned a < ((V 10%nat) + 32) + 8) -> ~ (((V 34%nat) - 32) <= bv_unsigned a < ((V 34%nat) - 32) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 10%nat) + 32) <= i < ((V 10%nat) + 32) + 8) -> ~ (((V 34%nat) - 32) <= i < ((V 34%nat) - 32) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x35814 M) (st fx' R' 0x35870 M')
        /\ (forall x, In x KS_encEAJ2w -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 34%nat) - 24)
        /\ L5.u64_at RSEGS M' ((V 34%nat) - 32) 0
        /\ L5.u64_at RSEGS M' ((V 10%nat) + 32) ((V 34%nat) - 24)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G10 pvzI9 K1 K2 pvzI10 K4 K5 K6 K7 pvzI11 K9 K10 pvzI12 K12 pvzI13 K14 K15 K16 K17 K18 K19 K20.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV44l; move HV44l before pvzI5; pose proof (proj2 pvzI5) as HV44r; move HV44r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV45l; move HV45l before pvzI6; pose proof (proj2 pvzI6) as HV45r; move HV45r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV46l; move HV46l before pvzI7; pose proof (proj2 pvzI7) as HV46r; move HV46r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV55l; move HV55l before pvzI8; pose proof (proj2 pvzI8) as HV55r; move HV55r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K0l; move K0l before pvzI9; pose proof (proj2 pvzI9) as K0r; move K0r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K8l; move K8l before pvzI11; pose proof (proj2 pvzI11) as K8r; move K8r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K11l; move K11l before pvzI12; pose proof (proj2 pvzI12) as K11r; move K11r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K13l; move K13l before pvzI13; pose proof (proj2 pvzI13) as K13r; move K13r before pvzI13; clear pvzI13.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_55 := V 55%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 55%nat => Z_to_bv 64 vz_55 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 33%nat => vz_33 | 34%nat => vz_34 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 55%nat => vz_55 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 56%nat. }
  assert (HR: regs_ok E PencEAJ2w.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PencEAJ2w.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PencEAJ2w.kn0).
  { unfold know_ok, PencEAJ2w.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K15) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K15) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K15) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K15; lia | clear - HV2l HV2r K0l K0r K6 K15; lia | clear - HV2l HV2r K0l K0r K6 K15; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K16) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K16) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K16) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K3l K3r K6 K16; lia | clear - HV10l HV10r K3l K3r K6 K16; lia | clear - HV10l HV10r K3l K3r K6 K16; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K16) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K16) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K13l K13r) | clear - HV10l HV10r K3l K3r K6 K16; lia | clear - HV10l HV10r K3l K3r K6 K16; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K13l K13r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K13l K13r) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K16) | evalEk ZA ltac:(clear - HV34l HV34r K11l K11r K13l K13r K15 K16) | clear - HV10l HV10r K3l K3r K6 K16; lia | clear - HV10l HV10r K3l K3r K6 K16; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K11l K11r K13l K13r K15 K16) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K11l K11r K13l K13r K15 K16) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K13l K13r HV34l HV34r K11l K11r K15 K16) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV34l HV34r K11l K11r K13l K13r K15 K16) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K11l K11r K13l K13r K15 K16; lia | clear - HV34l HV34r K11l K11r K13l K13r K15 K16; lia | clear - HV34l HV34r K11l K11r K13l K13r K15 K16; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K11l K11r K13l K13r K15 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K15) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K11l K11r K13l K13r K15 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K16) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K11l K11r K13l K13r K15 K16) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K11l K11r K13l K13r K15 K16; lia | clear - HV34l HV34r K11l K11r K13l K13r K15 K16; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K15) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K6 K15; lia | clear - HV2l HV2r K0l K0r K6 K15; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K15) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K6 K15; lia | clear - HV2l HV2r K0l K0r K6 K15; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K15) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K6 K15; lia | clear - HV2l HV2r K0l K0r K6 K15; lia | exactA K20]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PencEAJ2w.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PencEAJ2w.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_10 + 32) <= bv_unsigned a < (vz_10 + 32) + 8) -> ~ ((vz_34 - 32) <= bv_unsigned a < (vz_34 - 32) + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PencEAJ2w.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6 K16) | evalEk' ZA Hag ltac:(clear) | clear - HV10l HV10r K3l K3r K6 K16 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV34l HV34r K11l K11r K13l K13r K15 K16) | evalEk' ZA Hag ltac:(clear) | clear - HV34l HV34r K11l K11r K13l K13r K15 K16 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PencEAJ2w.ps0) with 0x35870 in Hms. change (SR.ps_regs PencEAJ2w.ps0) with (map (fun i => (i, nth i PencEAJ2w.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PencEAJ2w.ps0) with PencEAJ2w.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PencEAJ2w.regs0 PencEAJ2w.regs_out0 60 KS_encEAJ2w KS_encEAJ2w_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PencEAJ2w.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PencEAJ2w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEAJ2w.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PencEAJ2w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEAJ2w.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PencEAJ2w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEAJ2w.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PencEAJ2w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEAJ2w.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PencEAJ2w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEAJ2w.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PencEAJ2w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEAJ2w.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PencEAJ2w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV34l HV34r K11l K11r K13l K13r K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6 K16) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K11l K11r K13l K13r K15 K16) | clear; lia].
Qed.

Module PencEAR := BndP_Es_004S8.LibSegEs_encEAR.
Definition KS_encEAR : list nat := Eval vm_compute in (BG.kept_list 60 PencEAR.regs0 PencEAR.regs_out0).
Lemma KS_encEAR_ok : BG.kept_ok 60 PencEAR.regs0 PencEAR.regs_out0 KS_encEAR = true. Proof. vm_compute. reflexivity. Qed.
Lemma encEAR_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3585c M) (st fx' R' 0x35870 M')
        /\ (forall x, In x KS_encEAR -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G10 pvzI7 K1 K2 K3 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV44l; move HV44l before pvzI3; pose proof (proj2 pvzI3) as HV44r; move HV44r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV45l; move HV45l before pvzI4; pose proof (proj2 pvzI4) as HV45r; move HV45r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV46l; move HV46l before pvzI5; pose proof (proj2 pvzI5) as HV46r; move HV46r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV55l; move HV55l before pvzI6; pose proof (proj2 pvzI6) as HV55r; move HV55r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_55 := V 55%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 55%nat => Z_to_bv 64 vz_55 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 55%nat => vz_55 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 56%nat. }
  assert (HR: regs_ok E PencEAR.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PencEAR.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PencEAR.kn0).
  { unfold know_ok, PencEAR.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PencEAR.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PencEAR.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PencEAR.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PencEAR.ps0) with 0x35870 in Hms. change (SR.ps_regs PencEAR.ps0) with (map (fun i => (i, nth i PencEAR.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PencEAR.ps0) with PencEAR.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PencEAR.regs0 PencEAR.regs_out0 60 KS_encEAR KS_encEAR_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PencEAR.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PencEAR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEAR.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PencEAR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEAR.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PencEAR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEAR.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PencEAR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PencEAR.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PencEAR.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PencEOCe10 := BndP_Es_004S8.LibSegEs_encEOCe10.
Definition KS_encEOCe10 : list nat := Eval vm_compute in (BG.kept_list 60 PencEOCe10.regs0 PencEOCe10.regs_out0).
Lemma KS_encEOCe10_ok : BG.kept_ok 60 PencEOCe10.regs0 PencEOCe10.regs_out0 KS_encEOCe10 = true. Proof. vm_compute. reflexivity. Qed.
Lemma encEOCe10_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 24) (V 33%nat) -> 4096 <= (V 33%nat) <= 140737488355328 ->
  aligned (V 33%nat) 8 -> L5.u32_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 48) (V 36%nat) -> 1 <= (V 36%nat) <= 1025 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 32) ((V 33%nat) + 24) ->
  L5.u32_at RSEGS M (V 33%nat) 0 -> L5.u64_at RSEGS M ((V 33%nat) + 8) (V 38%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 16) (V 38%nat) -> 0 <= (V 38%nat) <= 16777216 ->
  ((V 33%nat) + 24 <= ((V 2%nat) - 48) \/ ((V 2%nat) - 48) + 48 <= (V 33%nat)) -> ((V 33%nat) + 24 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= (V 33%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> ~ (((bv_unsigned (getr R (reg 10))) + 32) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= i < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> ~ (((bv_unsigned (getr R (reg 10))) + 32) <= i < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x35f30 M) (st fx' R' 0x35fdc M')
        /\ (forall x, In x KS_encEOCe10 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 38%nat)
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 32) (V 33%nat)
        /\ L5.u32_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 48) ((V 36%nat) - 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 pvzI6 K1 K2 pvzI7 K4 K5 K6 K7 pvzI8 K9 K10 pvzI9 K12 K13 pvzI10 K15 K16 K17 K18 pvzI11 K20 K21.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV41l; move HV41l before pvzI5; pose proof (proj2 pvzI5) as HV41r; move HV41r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K8l; move K8l before pvzI8; pose proof (proj2 pvzI8) as K8r; move K8r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K11l; move K11l before pvzI9; pose proof (proj2 pvzI9) as K11r; move K11r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K14l; move K14l before pvzI10; pose proof (proj2 pvzI10) as K14r; move K14r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K19l; move K19l before pvzI11; pose proof (proj2 pvzI11) as K19r; move K19r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_41 := V 41%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 41%nat => Z_to_bv 64 vz_41 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 36%nat => vz_36 | 38%nat => vz_38 | 41%nat => vz_41 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E PencEOCe10.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PencEOCe10.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PencEOCe10.kn0).
  { unfold know_ok, PencEOCe10.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K20) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K20) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K20) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K20; lia | clear - HV2l HV2r K0l K0r K6 K20; lia | clear - HV2l HV2r K0l K0r K6 K20; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K3l K3r K6 K21) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K3l K3r K6 K21) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K3l K3r K6 K21) | evalEk ZA ltac:(clear) | clear - K3l K3r K6 K21; lia | clear - K3l K3r K6 K21; lia | clear - K3l K3r K6 K21; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K21) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K21) | evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear - K3l K3r K6 K21; lia | clear - K3l K3r K6 K21; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K21) | evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K20 K21) | clear - K3l K3r K6 K21; lia | clear - K3l K3r K6 K21; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K20 K21) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K20 K21) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - K3l K3r K6 K21) | evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | clear - K3l K3r K6 K21; lia | clear - K3l K3r K6 K21; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K21) | evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K20 K21) | clear - K3l K3r K6 K21; lia | clear - K3l K3r K6 K21; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K20 K21) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K11l K11r K20 K21; lia | clear - HV33l HV33r K11l K11r K20 K21; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K20 K21) | evalEk ZA ltac:(clear - HV38l HV38r K19l K19r) | clear - HV33l HV33r K11l K11r K20 K21; lia | clear - HV33l HV33r K11l K11r K20 K21; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K20 K21) | evalEk ZA ltac:(clear - HV38l HV38r K19l K19r) | clear - HV33l HV33r K11l K11r K20 K21; lia | clear - HV33l HV33r K11l K11r K20 K21; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K20 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K20) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K20 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K21) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PencEOCe10.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PencEOCe10.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> ~ (((bv_unsigned (getr R (reg 10))) + 32) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PencEOCe10.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K20) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K20 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K6 K21) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K6 K21 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K6 K21) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K6 K21 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PencEOCe10.ps0) with 0x35fdc in Hms. change (SR.ps_regs PencEOCe10.ps0) with (map (fun i => (i, nth i PencEOCe10.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PencEOCe10.ps0) with PencEOCe10.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PencEOCe10.regs0 PencEOCe10.regs_out0 60 KS_encEOCe10 KS_encEOCe10_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PencEOCe10.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PencEOCe10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOCe10.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PencEOCe10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOCe10.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PencEOCe10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOCe10.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PencEOCe10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOCe10.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PencEOCe10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K21) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K11l K11r K20 K21) | clear; lia]. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K21) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K14l K14r) | clear; lia].
Qed.

Module PencEOCe12 := BndP_Es_004S8.LibSegEs_encEOCe12.
Definition KS_encEOCe12 : list nat := Eval vm_compute in (BG.kept_list 60 PencEOCe12.regs0 PencEOCe12.regs_out0).
Lemma KS_encEOCe12_ok : BG.kept_ok 60 PencEOCe12.regs0 PencEOCe12.regs_out0 KS_encEOCe12 = true. Proof. vm_compute. reflexivity. Qed.
Lemma encEOCe12_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 24) (V 33%nat) -> 4096 <= (V 33%nat) <= 140737488355328 ->
  aligned (V 33%nat) 8 -> L5.u32_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 48) (V 36%nat) -> 1 <= (V 36%nat) <= 1025 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 32) ((V 33%nat) + 24) ->
  L5.u32_at RSEGS M (V 33%nat) 2 -> L5.u64_at RSEGS M ((V 33%nat) + 8) (V 38%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 16) (V 38%nat) -> 0 <= (V 38%nat) <= 16777216 ->
  ((V 33%nat) + 24 <= ((V 2%nat) - 48) \/ ((V 2%nat) - 48) + 48 <= (V 33%nat)) -> ((V 33%nat) + 24 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= (V 33%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> ~ (((bv_unsigned (getr R (reg 10))) + 32) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= i < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> ~ (((bv_unsigned (getr R (reg 10))) + 32) <= i < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x35f30 M) (st fx' R' 0x35fdc M')
        /\ (forall x, In x KS_encEOCe12 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 38%nat)
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 32) (V 33%nat)
        /\ L5.u32_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 48) ((V 36%nat) - 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 pvzI6 K1 K2 pvzI7 K4 K5 K6 K7 pvzI8 K9 K10 pvzI9 K12 K13 pvzI10 K15 K16 K17 K18 pvzI11 K20 K21.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV41l; move HV41l before pvzI5; pose proof (proj2 pvzI5) as HV41r; move HV41r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K8l; move K8l before pvzI8; pose proof (proj2 pvzI8) as K8r; move K8r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K11l; move K11l before pvzI9; pose proof (proj2 pvzI9) as K11r; move K11r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K14l; move K14l before pvzI10; pose proof (proj2 pvzI10) as K14r; move K14r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K19l; move K19l before pvzI11; pose proof (proj2 pvzI11) as K19r; move K19r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_41 := V 41%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 41%nat => Z_to_bv 64 vz_41 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 36%nat => vz_36 | 38%nat => vz_38 | 41%nat => vz_41 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E PencEOCe12.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PencEOCe12.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PencEOCe12.kn0).
  { unfold know_ok, PencEOCe12.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K20) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K20) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K20) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K20; lia | clear - HV2l HV2r K0l K0r K6 K20; lia | clear - HV2l HV2r K0l K0r K6 K20; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K3l K3r K6 K21) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K3l K3r K6 K21) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K3l K3r K6 K21) | evalEk ZA ltac:(clear) | clear - K3l K3r K6 K21; lia | clear - K3l K3r K6 K21; lia | clear - K3l K3r K6 K21; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K21) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K21) | evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear - K3l K3r K6 K21; lia | clear - K3l K3r K6 K21; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K21) | evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K20 K21) | clear - K3l K3r K6 K21; lia | clear - K3l K3r K6 K21; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K20 K21) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K20 K21) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - K3l K3r K6 K21) | evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | clear - K3l K3r K6 K21; lia | clear - K3l K3r K6 K21; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K21) | evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K20 K21) | clear - K3l K3r K6 K21; lia | clear - K3l K3r K6 K21; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K20 K21) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K11l K11r K20 K21; lia | clear - HV33l HV33r K11l K11r K20 K21; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K20 K21) | evalEk ZA ltac:(clear - HV38l HV38r K19l K19r) | clear - HV33l HV33r K11l K11r K20 K21; lia | clear - HV33l HV33r K11l K11r K20 K21; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K20 K21) | evalEk ZA ltac:(clear - HV38l HV38r K19l K19r) | clear - HV33l HV33r K11l K11r K20 K21; lia | clear - HV33l HV33r K11l K11r K20 K21; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K20 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K20) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K20 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K21) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PencEOCe12.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PencEOCe12.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> ~ (((bv_unsigned (getr R (reg 10))) + 32) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PencEOCe12.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K20) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K20 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K6 K21) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K6 K21 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K6 K21) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K6 K21 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PencEOCe12.ps0) with 0x35fdc in Hms. change (SR.ps_regs PencEOCe12.ps0) with (map (fun i => (i, nth i PencEOCe12.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PencEOCe12.ps0) with PencEOCe12.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PencEOCe12.regs0 PencEOCe12.regs_out0 60 KS_encEOCe12 KS_encEOCe12_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PencEOCe12.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PencEOCe12.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOCe12.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PencEOCe12.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOCe12.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PencEOCe12.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOCe12.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PencEOCe12.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOCe12.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PencEOCe12.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K21) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K11l K11r K20 K21) | clear; lia]. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K21) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K14l K14r) | clear; lia].
Qed.

Module PencEOCe20 := BndP_Es_004S8.LibSegEs_encEOCe20.
Definition KS_encEOCe20 : list nat := Eval vm_compute in (BG.kept_list 60 PencEOCe20.regs0 PencEOCe20.regs_out0).
Lemma KS_encEOCe20_ok : BG.kept_ok 60 PencEOCe20.regs0 PencEOCe20.regs_out0 KS_encEOCe20 = true. Proof. vm_compute. reflexivity. Qed.
Lemma encEOCe20_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 24) (V 33%nat) -> 4096 <= (V 33%nat) <= 140737488355328 ->
  aligned (V 33%nat) 8 -> L5.u32_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 48) (V 36%nat) -> 1 <= (V 36%nat) <= 1025 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 32) (V 34%nat) ->
  4144 <= (V 34%nat) <= 140737488355328 -> aligned (V 34%nat) 8 -> 48 <= ((V 34%nat) - (V 33%nat)) <= 100000 -> L5.u32_at RSEGS M ((V 34%nat) - 24) 0 ->
  L5.u64_at RSEGS M ((V 34%nat) - 16) (V 38%nat) -> L5.u64_at RSEGS M ((V 34%nat) - 8) (V 38%nat) -> L5.u64_at RSEGS M ((V 34%nat) - 32) (V 42%nat) -> 0 <= (V 42%nat) <= 18446744073709551614 ->
  0 <= (V 38%nat) <= 16777216 -> L5.writable RSEGS M ((V 34%nat) - 48) 48 -> (((V 34%nat) - 48) + 48 <= ((V 2%nat) - 48) \/ ((V 2%nat) - 48) + 48 <= ((V 34%nat) - 48)) -> (((V 34%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 34%nat) - 48)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> ~ (((bv_unsigned (getr R (reg 10))) + 32) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> ~ (((V 34%nat) - 32) <= bv_unsigned a < ((V 34%nat) - 32) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= i < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> ~ (((bv_unsigned (getr R (reg 10))) + 32) <= i < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> ~ (((V 34%nat) - 32) <= i < ((V 34%nat) - 32) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x35f30 M) (st fx' R' 0x35fdc M')
        /\ (forall x, In x KS_encEOCe20 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 42%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 34%nat) - 24)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 34%nat) - 32) ((V 42%nat) + 1)
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 32) ((V 34%nat) - 24)
        /\ L5.u32_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 48) ((V 36%nat) - 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 pvzI8 K1 K2 pvzI9 K4 K5 K6 K7 pvzI10 K9 K10 pvzI11 K12 K13 pvzI12 K15 pvzI13 K17 pvzI14 K19 K20 K21 K22 pvzI15 pvzI16 K25 K26 K27.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV41l; move HV41l before pvzI6; pose proof (proj2 pvzI6) as HV41r; move HV41r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV42l; move HV42l before pvzI7; pose proof (proj2 pvzI7) as HV42r; move HV42r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K8l; move K8l before pvzI10; pose proof (proj2 pvzI10) as K8r; move K8r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K11l; move K11l before pvzI11; pose proof (proj2 pvzI11) as K11r; move K11r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K14l; move K14l before pvzI12; pose proof (proj2 pvzI12) as K14r; move K14r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K16l; move K16l before pvzI13; pose proof (proj2 pvzI13) as K16r; move K16r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K18l; move K18l before pvzI14; pose proof (proj2 pvzI14) as K18r; move K18r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K23l; move K23l before pvzI15; pose proof (proj2 pvzI15) as K23r; move K23r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K24l; move K24l before pvzI16; pose proof (proj2 pvzI16) as K24r; move K24r before pvzI16; clear pvzI16.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 38%nat => vz_38 | 41%nat => vz_41 | 42%nat => vz_42 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 43%nat. }
  assert (HR: regs_ok E PencEOCe20.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PencEOCe20.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PencEOCe20.kn0).
  { unfold know_ok, PencEOCe20.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K26) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K26) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K26) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K26; lia | clear - HV2l HV2r K0l K0r K6 K26; lia | clear - HV2l HV2r K0l K0r K6 K26; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K3l K3r K6 K27) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K3l K3r K6 K27) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K3l K3r K6 K27) | evalEk ZA ltac:(clear) | clear - K3l K3r K6 K27; lia | clear - K3l K3r K6 K27; lia | clear - K3l K3r K6 K27; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K27) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K27) | evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear - K3l K3r K6 K27; lia | clear - K3l K3r K6 K27; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K27) | evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear - K3l K3r K6 K27; lia | clear - K3l K3r K6 K27; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - K3l K3r K6 K27) | evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | clear - K3l K3r K6 K27; lia | clear - K3l K3r K6 K27; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K27) | evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | clear - K3l K3r K6 K27; lia | clear - K3l K3r K6 K27; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r HV34l HV34r K16l K16r K26 K27) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K16l K16r K18l K18r K26 K27; lia | clear - HV34l HV34r K16l K16r K18l K18r K26 K27; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | evalEk ZA ltac:(clear - HV38l HV38r K24l K24r) | clear - HV34l HV34r K16l K16r K18l K18r K26 K27; lia | clear - HV34l HV34r K16l K16r K18l K18r K26 K27; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | evalEk ZA ltac:(clear - HV38l HV38r K24l K24r) | clear - HV34l HV34r K16l K16r K18l K18r K26 K27; lia | clear - HV34l HV34r K16l K16r K18l K18r K26 K27; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | evalEk ZA ltac:(clear - HV42l HV42r K23l K23r) | clear - HV34l HV34r K16l K16r K18l K18r K26 K27; lia | clear - HV34l HV34r K16l K16r K18l K18r K26 K27; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K24l K24r) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K16l K16r K18l K18r K26 K27; lia | clear - HV34l HV34r K16l K16r K18l K18r K26 K27; lia | clear - HV34l HV34r K16l K16r K18l K18r K26 K27; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K26) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K27) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PencEOCe20.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PencEOCe20.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> ~ (((bv_unsigned (getr R (reg 10))) + 32) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> ~ ((vz_34 - 32) <= bv_unsigned a < (vz_34 - 32) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PencEOCe20.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K26 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K6 K27) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K6 K27 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K6 K27) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K6 K27 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | evalEk' ZA Hag ltac:(clear) | clear - HV34l HV34r K16l K16r K18l K18r K26 K27 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PencEOCe20.ps0) with 0x35fdc in Hms. change (SR.ps_regs PencEOCe20.ps0) with (map (fun i => (i, nth i PencEOCe20.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PencEOCe20.ps0) with PencEOCe20.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PencEOCe20.regs0 PencEOCe20.regs_out0 60 KS_encEOCe20 KS_encEOCe20_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PencEOCe20.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PencEOCe20.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOCe20.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PencEOCe20.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOCe20.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PencEOCe20.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOCe20.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PencEOCe20.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOCe20.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PencEOCe20.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | evalEk' ZA Hag ltac:(clear - HV42l HV42r K23l K23r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K27) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | clear; lia]. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K27) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K14l K14r) | clear; lia].
Qed.

Module PencEOCe20w := BndP_Es_004S8.LibSegEs_encEOCe20w.
Definition KS_encEOCe20w : list nat := Eval vm_compute in (BG.kept_list 60 PencEOCe20w.regs0 PencEOCe20w.regs_out0).
Lemma KS_encEOCe20w_ok : BG.kept_ok 60 PencEOCe20w.regs0 PencEOCe20w.regs_out0 KS_encEOCe20w = true. Proof. vm_compute. reflexivity. Qed.
Lemma encEOCe20w_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 24) (V 33%nat) -> 4096 <= (V 33%nat) <= 140737488355328 ->
  aligned (V 33%nat) 8 -> L5.u32_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 48) (V 36%nat) -> 1 <= (V 36%nat) <= 1025 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 32) (V 34%nat) ->
  4144 <= (V 34%nat) <= 140737488355328 -> aligned (V 34%nat) 8 -> 48 <= ((V 34%nat) - (V 33%nat)) <= 100000 -> L5.u32_at RSEGS M ((V 34%nat) - 24) 0 ->
  L5.u64_at RSEGS M ((V 34%nat) - 16) (V 38%nat) -> L5.u64_at RSEGS M ((V 34%nat) - 8) (V 38%nat) -> L5.u64_at RSEGS M ((V 34%nat) - 32) 18446744073709551615 -> 0 <= (V 38%nat) <= 16777216 ->
  L5.writable RSEGS M ((V 34%nat) - 48) 48 -> (((V 34%nat) - 48) + 48 <= ((V 2%nat) - 48) \/ ((V 2%nat) - 48) + 48 <= ((V 34%nat) - 48)) -> (((V 34%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 34%nat) - 48)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> ~ (((bv_unsigned (getr R (reg 10))) + 32) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> ~ (((V 34%nat) - 32) <= bv_unsigned a < ((V 34%nat) - 32) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= i < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> ~ (((bv_unsigned (getr R (reg 10))) + 32) <= i < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> ~ (((V 34%nat) - 32) <= i < ((V 34%nat) - 32) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x35f30 M) (st fx' R' 0x35fdc M')
        /\ (forall x, In x KS_encEOCe20w -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 34%nat) - 24)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 34%nat) - 32) 0
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 32) ((V 34%nat) - 24)
        /\ L5.u32_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 48) ((V 36%nat) - 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 pvzI7 K1 K2 pvzI8 K4 K5 K6 K7 pvzI9 K9 K10 pvzI10 K12 K13 pvzI11 K15 pvzI12 K17 pvzI13 K19 K20 K21 K22 pvzI14 K24 K25 K26.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV41l; move HV41l before pvzI6; pose proof (proj2 pvzI6) as HV41r; move HV41r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K8l; move K8l before pvzI9; pose proof (proj2 pvzI9) as K8r; move K8r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K11l; move K11l before pvzI10; pose proof (proj2 pvzI10) as K11r; move K11r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K14l; move K14l before pvzI11; pose proof (proj2 pvzI11) as K14r; move K14r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K16l; move K16l before pvzI12; pose proof (proj2 pvzI12) as K16r; move K16r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K18l; move K18l before pvzI13; pose proof (proj2 pvzI13) as K18r; move K18r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K23l; move K23l before pvzI14; pose proof (proj2 pvzI14) as K23r; move K23r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_41 := V 41%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 41%nat => Z_to_bv 64 vz_41 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 38%nat => vz_38 | 41%nat => vz_41 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E PencEOCe20w.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PencEOCe20w.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PencEOCe20w.kn0).
  { unfold know_ok, PencEOCe20w.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K25) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K25) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K25) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K25; lia | clear - HV2l HV2r K0l K0r K6 K25; lia | clear - HV2l HV2r K0l K0r K6 K25; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K3l K3r K6 K26) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K3l K3r K6 K26) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K3l K3r K6 K26) | evalEk ZA ltac:(clear) | clear - K3l K3r K6 K26; lia | clear - K3l K3r K6 K26; lia | clear - K3l K3r K6 K26; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K25) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K26) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K26) | evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear - K3l K3r K6 K26; lia | clear - K3l K3r K6 K26; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K26) | evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear - K3l K3r K6 K26; lia | clear - K3l K3r K6 K26; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - K3l K3r K6 K26) | evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | clear - K3l K3r K6 K26; lia | clear - K3l K3r K6 K26; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K26) | evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | clear - K3l K3r K6 K26; lia | clear - K3l K3r K6 K26; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r HV34l HV34r K16l K16r K25 K26) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K16l K16r K18l K18r K25 K26; lia | clear - HV34l HV34r K16l K16r K18l K18r K25 K26; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | evalEk ZA ltac:(clear - HV38l HV38r K23l K23r) | clear - HV34l HV34r K16l K16r K18l K18r K25 K26; lia | clear - HV34l HV34r K16l K16r K18l K18r K25 K26; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | evalEk ZA ltac:(clear - HV38l HV38r K23l K23r) | clear - HV34l HV34r K16l K16r K18l K18r K25 K26; lia | clear - HV34l HV34r K16l K16r K18l K18r K25 K26; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K16l K16r K18l K18r K25 K26; lia | clear - HV34l HV34r K16l K16r K18l K18r K25 K26; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K16l K16r K18l K18r K25 K26; lia | clear - HV34l HV34r K16l K16r K18l K18r K25 K26; lia | clear - HV34l HV34r K16l K16r K18l K18r K25 K26; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K25) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K26) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PencEOCe20w.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PencEOCe20w.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> ~ (((bv_unsigned (getr R (reg 10))) + 32) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> ~ ((vz_34 - 32) <= bv_unsigned a < (vz_34 - 32) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PencEOCe20w.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K25) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K25 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K6 K26) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K6 K26 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K6 K26) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K6 K26 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV34l HV34r K16l K16r K18l K18r K25 K26 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PencEOCe20w.ps0) with 0x35fdc in Hms. change (SR.ps_regs PencEOCe20w.ps0) with (map (fun i => (i, nth i PencEOCe20w.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PencEOCe20w.ps0) with PencEOCe20w.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PencEOCe20w.regs0 PencEOCe20w.regs_out0 60 KS_encEOCe20w KS_encEOCe20w_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PencEOCe20w.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PencEOCe20w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOCe20w.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PencEOCe20w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOCe20w.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PencEOCe20w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOCe20w.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PencEOCe20w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOCe20w.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PencEOCe20w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K26) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | clear; lia]. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K26) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K14l K14r) | clear; lia].
Qed.

Module PencEOCe22 := BndP_Es_004S8.LibSegEs_encEOCe22.
Definition KS_encEOCe22 : list nat := Eval vm_compute in (BG.kept_list 60 PencEOCe22.regs0 PencEOCe22.regs_out0).
Lemma KS_encEOCe22_ok : BG.kept_ok 60 PencEOCe22.regs0 PencEOCe22.regs_out0 KS_encEOCe22 = true. Proof. vm_compute. reflexivity. Qed.
Lemma encEOCe22_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 24) (V 33%nat) -> 4096 <= (V 33%nat) <= 140737488355328 ->
  aligned (V 33%nat) 8 -> L5.u32_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 48) (V 36%nat) -> 1 <= (V 36%nat) <= 1025 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 32) (V 34%nat) ->
  4144 <= (V 34%nat) <= 140737488355328 -> aligned (V 34%nat) 8 -> 48 <= ((V 34%nat) - (V 33%nat)) <= 100000 -> L5.u32_at RSEGS M ((V 34%nat) - 24) 2 ->
  L5.u64_at RSEGS M ((V 34%nat) - 16) (V 38%nat) -> L5.u64_at RSEGS M ((V 34%nat) - 8) (V 38%nat) -> L5.u64_at RSEGS M ((V 34%nat) - 32) (V 42%nat) -> 0 <= (V 42%nat) <= 18446744073709551614 ->
  0 <= (V 38%nat) <= 16777216 -> L5.writable RSEGS M ((V 34%nat) - 48) 48 -> (((V 34%nat) - 48) + 48 <= ((V 2%nat) - 48) \/ ((V 2%nat) - 48) + 48 <= ((V 34%nat) - 48)) -> (((V 34%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 34%nat) - 48)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> ~ (((bv_unsigned (getr R (reg 10))) + 32) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> ~ (((V 34%nat) - 32) <= bv_unsigned a < ((V 34%nat) - 32) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= i < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> ~ (((bv_unsigned (getr R (reg 10))) + 32) <= i < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> ~ (((V 34%nat) - 32) <= i < ((V 34%nat) - 32) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x35f30 M) (st fx' R' 0x35fdc M')
        /\ (forall x, In x KS_encEOCe22 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 42%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 34%nat) - 24)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 34%nat) - 32) ((V 42%nat) + 1)
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 32) ((V 34%nat) - 24)
        /\ L5.u32_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 48) ((V 36%nat) - 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 pvzI8 K1 K2 pvzI9 K4 K5 K6 K7 pvzI10 K9 K10 pvzI11 K12 K13 pvzI12 K15 pvzI13 K17 pvzI14 K19 K20 K21 K22 pvzI15 pvzI16 K25 K26 K27.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV41l; move HV41l before pvzI6; pose proof (proj2 pvzI6) as HV41r; move HV41r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV42l; move HV42l before pvzI7; pose proof (proj2 pvzI7) as HV42r; move HV42r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K8l; move K8l before pvzI10; pose proof (proj2 pvzI10) as K8r; move K8r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K11l; move K11l before pvzI11; pose proof (proj2 pvzI11) as K11r; move K11r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K14l; move K14l before pvzI12; pose proof (proj2 pvzI12) as K14r; move K14r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K16l; move K16l before pvzI13; pose proof (proj2 pvzI13) as K16r; move K16r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K18l; move K18l before pvzI14; pose proof (proj2 pvzI14) as K18r; move K18r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K23l; move K23l before pvzI15; pose proof (proj2 pvzI15) as K23r; move K23r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K24l; move K24l before pvzI16; pose proof (proj2 pvzI16) as K24r; move K24r before pvzI16; clear pvzI16.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 38%nat => vz_38 | 41%nat => vz_41 | 42%nat => vz_42 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 43%nat. }
  assert (HR: regs_ok E PencEOCe22.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PencEOCe22.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PencEOCe22.kn0).
  { unfold know_ok, PencEOCe22.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K26) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K26) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K26) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K26; lia | clear - HV2l HV2r K0l K0r K6 K26; lia | clear - HV2l HV2r K0l K0r K6 K26; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K3l K3r K6 K27) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K3l K3r K6 K27) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K3l K3r K6 K27) | evalEk ZA ltac:(clear) | clear - K3l K3r K6 K27; lia | clear - K3l K3r K6 K27; lia | clear - K3l K3r K6 K27; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K27) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K27) | evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear - K3l K3r K6 K27; lia | clear - K3l K3r K6 K27; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K27) | evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear - K3l K3r K6 K27; lia | clear - K3l K3r K6 K27; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - K3l K3r K6 K27) | evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | clear - K3l K3r K6 K27; lia | clear - K3l K3r K6 K27; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K27) | evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | clear - K3l K3r K6 K27; lia | clear - K3l K3r K6 K27; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r HV34l HV34r K16l K16r K26 K27) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K16l K16r K18l K18r K26 K27; lia | clear - HV34l HV34r K16l K16r K18l K18r K26 K27; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | evalEk ZA ltac:(clear - HV38l HV38r K24l K24r) | clear - HV34l HV34r K16l K16r K18l K18r K26 K27; lia | clear - HV34l HV34r K16l K16r K18l K18r K26 K27; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | evalEk ZA ltac:(clear - HV38l HV38r K24l K24r) | clear - HV34l HV34r K16l K16r K18l K18r K26 K27; lia | clear - HV34l HV34r K16l K16r K18l K18r K26 K27; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | evalEk ZA ltac:(clear - HV42l HV42r K23l K23r) | clear - HV34l HV34r K16l K16r K18l K18r K26 K27; lia | clear - HV34l HV34r K16l K16r K18l K18r K26 K27; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K24l K24r) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K16l K16r K18l K18r K26 K27; lia | clear - HV34l HV34r K16l K16r K18l K18r K26 K27; lia | clear - HV34l HV34r K16l K16r K18l K18r K26 K27; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K26) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K27) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PencEOCe22.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PencEOCe22.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> ~ (((bv_unsigned (getr R (reg 10))) + 32) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> ~ ((vz_34 - 32) <= bv_unsigned a < (vz_34 - 32) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PencEOCe22.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K26 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K6 K27) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K6 K27 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K6 K27) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K6 K27 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | evalEk' ZA Hag ltac:(clear) | clear - HV34l HV34r K16l K16r K18l K18r K26 K27 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PencEOCe22.ps0) with 0x35fdc in Hms. change (SR.ps_regs PencEOCe22.ps0) with (map (fun i => (i, nth i PencEOCe22.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PencEOCe22.ps0) with PencEOCe22.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PencEOCe22.regs0 PencEOCe22.regs_out0 60 KS_encEOCe22 KS_encEOCe22_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PencEOCe22.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PencEOCe22.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOCe22.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PencEOCe22.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOCe22.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PencEOCe22.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOCe22.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PencEOCe22.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOCe22.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PencEOCe22.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | evalEk' ZA Hag ltac:(clear - HV42l HV42r K23l K23r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K27) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K16l K16r K18l K18r K26 K27) | clear; lia]. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K27) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K14l K14r) | clear; lia].
Qed.

Module PencEOCe22w := BndP_Es_004S8.LibSegEs_encEOCe22w.
Definition KS_encEOCe22w : list nat := Eval vm_compute in (BG.kept_list 60 PencEOCe22w.regs0 PencEOCe22w.regs_out0).
Lemma KS_encEOCe22w_ok : BG.kept_ok 60 PencEOCe22w.regs0 PencEOCe22w.regs_out0 KS_encEOCe22w = true. Proof. vm_compute. reflexivity. Qed.
Lemma encEOCe22w_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 24) (V 33%nat) -> 4096 <= (V 33%nat) <= 140737488355328 ->
  aligned (V 33%nat) 8 -> L5.u32_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 48) (V 36%nat) -> 1 <= (V 36%nat) <= 1025 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 32) (V 34%nat) ->
  4144 <= (V 34%nat) <= 140737488355328 -> aligned (V 34%nat) 8 -> 48 <= ((V 34%nat) - (V 33%nat)) <= 100000 -> L5.u32_at RSEGS M ((V 34%nat) - 24) 2 ->
  L5.u64_at RSEGS M ((V 34%nat) - 16) (V 38%nat) -> L5.u64_at RSEGS M ((V 34%nat) - 8) (V 38%nat) -> L5.u64_at RSEGS M ((V 34%nat) - 32) 18446744073709551615 -> 0 <= (V 38%nat) <= 16777216 ->
  L5.writable RSEGS M ((V 34%nat) - 48) 48 -> (((V 34%nat) - 48) + 48 <= ((V 2%nat) - 48) \/ ((V 2%nat) - 48) + 48 <= ((V 34%nat) - 48)) -> (((V 34%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 34%nat) - 48)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> ~ (((bv_unsigned (getr R (reg 10))) + 32) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> ~ (((V 34%nat) - 32) <= bv_unsigned a < ((V 34%nat) - 32) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= i < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> ~ (((bv_unsigned (getr R (reg 10))) + 32) <= i < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> ~ (((V 34%nat) - 32) <= i < ((V 34%nat) - 32) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x35f30 M) (st fx' R' 0x35fdc M')
        /\ (forall x, In x KS_encEOCe22w -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 34%nat) - 24)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 34%nat) - 32) 0
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 32) ((V 34%nat) - 24)
        /\ L5.u32_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 48) ((V 36%nat) - 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 pvzI7 K1 K2 pvzI8 K4 K5 K6 K7 pvzI9 K9 K10 pvzI10 K12 K13 pvzI11 K15 pvzI12 K17 pvzI13 K19 K20 K21 K22 pvzI14 K24 K25 K26.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV41l; move HV41l before pvzI6; pose proof (proj2 pvzI6) as HV41r; move HV41r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K8l; move K8l before pvzI9; pose proof (proj2 pvzI9) as K8r; move K8r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K11l; move K11l before pvzI10; pose proof (proj2 pvzI10) as K11r; move K11r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K14l; move K14l before pvzI11; pose proof (proj2 pvzI11) as K14r; move K14r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K16l; move K16l before pvzI12; pose proof (proj2 pvzI12) as K16r; move K16r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K18l; move K18l before pvzI13; pose proof (proj2 pvzI13) as K18r; move K18r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K23l; move K23l before pvzI14; pose proof (proj2 pvzI14) as K23r; move K23r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_41 := V 41%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 41%nat => Z_to_bv 64 vz_41 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 38%nat => vz_38 | 41%nat => vz_41 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E PencEOCe22w.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PencEOCe22w.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PencEOCe22w.kn0).
  { unfold know_ok, PencEOCe22w.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K25) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K25) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K25) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K25; lia | clear - HV2l HV2r K0l K0r K6 K25; lia | clear - HV2l HV2r K0l K0r K6 K25; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K3l K3r K6 K26) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K3l K3r K6 K26) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K3l K3r K6 K26) | evalEk ZA ltac:(clear) | clear - K3l K3r K6 K26; lia | clear - K3l K3r K6 K26; lia | clear - K3l K3r K6 K26; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K25) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K26) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K26) | evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear - K3l K3r K6 K26; lia | clear - K3l K3r K6 K26; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K26) | evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear - K3l K3r K6 K26; lia | clear - K3l K3r K6 K26; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - K3l K3r K6 K26) | evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | clear - K3l K3r K6 K26; lia | clear - K3l K3r K6 K26; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K26) | evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | clear - K3l K3r K6 K26; lia | clear - K3l K3r K6 K26; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r HV34l HV34r K16l K16r K25 K26) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K16l K16r K18l K18r K25 K26; lia | clear - HV34l HV34r K16l K16r K18l K18r K25 K26; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | evalEk ZA ltac:(clear - HV38l HV38r K23l K23r) | clear - HV34l HV34r K16l K16r K18l K18r K25 K26; lia | clear - HV34l HV34r K16l K16r K18l K18r K25 K26; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | evalEk ZA ltac:(clear - HV38l HV38r K23l K23r) | clear - HV34l HV34r K16l K16r K18l K18r K25 K26; lia | clear - HV34l HV34r K16l K16r K18l K18r K25 K26; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K16l K16r K18l K18r K25 K26; lia | clear - HV34l HV34r K16l K16r K18l K18r K25 K26; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K16l K16r K18l K18r K25 K26; lia | clear - HV34l HV34r K16l K16r K18l K18r K25 K26; lia | clear - HV34l HV34r K16l K16r K18l K18r K25 K26; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K25) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K26) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PencEOCe22w.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PencEOCe22w.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> ~ (((bv_unsigned (getr R (reg 10))) + 32) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> ~ ((vz_34 - 32) <= bv_unsigned a < (vz_34 - 32) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PencEOCe22w.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K25) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K25 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K6 K26) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K6 K26 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K6 K26) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K6 K26 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV34l HV34r K16l K16r K18l K18r K25 K26 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PencEOCe22w.ps0) with 0x35fdc in Hms. change (SR.ps_regs PencEOCe22w.ps0) with (map (fun i => (i, nth i PencEOCe22w.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PencEOCe22w.ps0) with PencEOCe22w.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PencEOCe22w.regs0 PencEOCe22w.regs_out0 60 KS_encEOCe22w KS_encEOCe22w_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PencEOCe22w.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PencEOCe22w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOCe22w.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PencEOCe22w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOCe22w.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PencEOCe22w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOCe22w.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PencEOCe22w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOCe22w.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PencEOCe22w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K26) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K16l K16r K18l K18r K25 K26) | clear; lia]. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K26) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K14l K14r) | clear; lia].
Qed.

Module PencEOCgt0 := BndP_Es_004S8.LibSegEs_encEOCgt0.
Definition KS_encEOCgt0 : list nat := Eval vm_compute in (BG.kept_list 60 PencEOCgt0.regs0 PencEOCgt0.regs_out0).
Lemma KS_encEOCgt0_ok : BG.kept_ok 60 PencEOCgt0.regs0 PencEOCgt0.regs_out0 KS_encEOCgt0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma encEOCgt0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 24) (V 33%nat) -> 4096 <= (V 33%nat) <= 140737488355328 ->
  aligned (V 33%nat) 8 -> L5.u32_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 48) (V 36%nat) -> 1 <= (V 36%nat) <= 1025 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 32) (V 34%nat) ->
  4120 <= (V 34%nat) <= 140737488355328 -> aligned (V 34%nat) 8 -> 24 <= ((V 34%nat) - (V 33%nat)) <= 100000 -> L5.u32_at RSEGS M ((V 34%nat) - 24) 0 ->
  L5.u64_at RSEGS M ((V 34%nat) - 16) (V 38%nat) -> 0 <= (V 38%nat) <= 16777216 -> (((V 34%nat) - 48) + 48 <= ((V 2%nat) - 48) \/ ((V 2%nat) - 48) + 48 <= ((V 34%nat) - 48)) -> (((V 34%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 34%nat) - 48)) ->
  L5.u64_at RSEGS M ((V 34%nat) - 8) ((V 38%nat) + (V 43%nat)) -> 1 <= (V 43%nat) <= 18446744073692774399 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= i < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x35f30 M) (st fx' R' 0x36f18 M')
        /\ (forall x, In x KS_encEOCgt0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 221128
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 10) = getr R (reg 12)
        /\ getr R' (reg 11) = Z_to_bv 64 8
        /\ getr R' (reg 13) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 38%nat) + (V 43%nat))
        /\ L5.u32_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 48) ((V 36%nat) - 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 pvzI8 K1 K2 pvzI9 K4 K5 K6 K7 pvzI10 K9 K10 pvzI11 K12 K13 pvzI12 K15 pvzI13 K17 pvzI14 K19 K20 pvzI15 K22 K23 K24 pvzI16.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV41l; move HV41l before pvzI6; pose proof (proj2 pvzI6) as HV41r; move HV41r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV43l; move HV43l before pvzI7; pose proof (proj2 pvzI7) as HV43r; move HV43r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K8l; move K8l before pvzI10; pose proof (proj2 pvzI10) as K8r; move K8r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K11l; move K11l before pvzI11; pose proof (proj2 pvzI11) as K11r; move K11r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K14l; move K14l before pvzI12; pose proof (proj2 pvzI12) as K14r; move K14r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K16l; move K16l before pvzI13; pose proof (proj2 pvzI13) as K16r; move K16r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K18l; move K18l before pvzI14; pose proof (proj2 pvzI14) as K18r; move K18r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K21l; move K21l before pvzI15; pose proof (proj2 pvzI15) as K21r; move K21r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K25l; move K25l before pvzI16; pose proof (proj2 pvzI16) as K25r; move K25r before pvzI16; clear pvzI16.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_43 := V 43%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 41%nat => Z_to_bv 64 vz_41 | 43%nat => Z_to_bv 64 vz_43 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 38%nat => vz_38 | 41%nat => vz_41 | 43%nat => vz_43 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E PencEOCgt0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PencEOCgt0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PencEOCgt0.kn0).
  { unfold know_ok, PencEOCgt0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K22; lia | clear - HV2l HV2r K0l K0r K6 K22; lia | clear - HV2l HV2r K0l K0r K6 K22; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r HV34l HV34r K16l K16r K22 K23) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear - HV38l HV38r K21l K21r) | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear - HV38l HV38r K21l K21r HV43l HV43r K25l K25r) | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PencEOCgt0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PencEOCgt0.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PencEOCgt0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K22 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K6 K23) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K6 K23 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PencEOCgt0.ps0) with 0x36f18 in Hms. change (SR.ps_regs PencEOCgt0.ps0) with (map (fun i => (i, nth i PencEOCgt0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PencEOCgt0.ps0) with PencEOCgt0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PencEOCgt0.regs0 PencEOCgt0.regs_out0 60 KS_encEOCgt0 KS_encEOCgt0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PencEOCgt0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PencEOCgt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOCgt0.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PencEOCgt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOCgt0.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PencEOCgt0.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PencEOCgt0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PencEOCgt0.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PencEOCgt0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PencEOCgt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOCgt0.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PencEOCgt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOCgt0.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PencEOCgt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K23) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K14l K14r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PencEOCgt2 := BndP_Es_004S8.LibSegEs_encEOCgt2.
Definition KS_encEOCgt2 : list nat := Eval vm_compute in (BG.kept_list 60 PencEOCgt2.regs0 PencEOCgt2.regs_out0).
Lemma KS_encEOCgt2_ok : BG.kept_ok 60 PencEOCgt2.regs0 PencEOCgt2.regs_out0 KS_encEOCgt2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma encEOCgt2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 24) (V 33%nat) -> 4096 <= (V 33%nat) <= 140737488355328 ->
  aligned (V 33%nat) 8 -> L5.u32_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 48) (V 36%nat) -> 1 <= (V 36%nat) <= 1025 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 32) (V 34%nat) ->
  4120 <= (V 34%nat) <= 140737488355328 -> aligned (V 34%nat) 8 -> 24 <= ((V 34%nat) - (V 33%nat)) <= 100000 -> L5.u32_at RSEGS M ((V 34%nat) - 24) 2 ->
  L5.u64_at RSEGS M ((V 34%nat) - 16) (V 38%nat) -> 0 <= (V 38%nat) <= 16777216 -> (((V 34%nat) - 48) + 48 <= ((V 2%nat) - 48) \/ ((V 2%nat) - 48) + 48 <= ((V 34%nat) - 48)) -> (((V 34%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 34%nat) - 48)) ->
  L5.u64_at RSEGS M ((V 34%nat) - 8) ((V 38%nat) + (V 43%nat)) -> 1 <= (V 43%nat) <= 18446744073692774399 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= i < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x35f30 M) (st fx' R' 0x36f18 M')
        /\ (forall x, In x KS_encEOCgt2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 221128
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 10) = getr R (reg 12)
        /\ getr R' (reg 11) = Z_to_bv 64 8
        /\ getr R' (reg 13) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 38%nat) + (V 43%nat))
        /\ L5.u32_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 48) ((V 36%nat) - 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 pvzI8 K1 K2 pvzI9 K4 K5 K6 K7 pvzI10 K9 K10 pvzI11 K12 K13 pvzI12 K15 pvzI13 K17 pvzI14 K19 K20 pvzI15 K22 K23 K24 pvzI16.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV41l; move HV41l before pvzI6; pose proof (proj2 pvzI6) as HV41r; move HV41r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV43l; move HV43l before pvzI7; pose proof (proj2 pvzI7) as HV43r; move HV43r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K8l; move K8l before pvzI10; pose proof (proj2 pvzI10) as K8r; move K8r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K11l; move K11l before pvzI11; pose proof (proj2 pvzI11) as K11r; move K11r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K14l; move K14l before pvzI12; pose proof (proj2 pvzI12) as K14r; move K14r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K16l; move K16l before pvzI13; pose proof (proj2 pvzI13) as K16r; move K16r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K18l; move K18l before pvzI14; pose proof (proj2 pvzI14) as K18r; move K18r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K21l; move K21l before pvzI15; pose proof (proj2 pvzI15) as K21r; move K21r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K25l; move K25l before pvzI16; pose proof (proj2 pvzI16) as K25r; move K25r before pvzI16; clear pvzI16.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_43 := V 43%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 41%nat => Z_to_bv 64 vz_41 | 43%nat => Z_to_bv 64 vz_43 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 38%nat => vz_38 | 41%nat => vz_41 | 43%nat => vz_43 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E PencEOCgt2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PencEOCgt2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PencEOCgt2.kn0).
  { unfold know_ok, PencEOCgt2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K22; lia | clear - HV2l HV2r K0l K0r K6 K22; lia | clear - HV2l HV2r K0l K0r K6 K22; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r HV34l HV34r K16l K16r K22 K23) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear - HV38l HV38r K21l K21r) | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear - HV38l HV38r K21l K21r HV43l HV43r K25l K25r) | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PencEOCgt2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PencEOCgt2.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PencEOCgt2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K22 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K6 K23) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K6 K23 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PencEOCgt2.ps0) with 0x36f18 in Hms. change (SR.ps_regs PencEOCgt2.ps0) with (map (fun i => (i, nth i PencEOCgt2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PencEOCgt2.ps0) with PencEOCgt2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PencEOCgt2.regs0 PencEOCgt2.regs_out0 60 KS_encEOCgt2 KS_encEOCgt2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PencEOCgt2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PencEOCgt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOCgt2.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PencEOCgt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOCgt2.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PencEOCgt2.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PencEOCgt2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PencEOCgt2.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PencEOCgt2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PencEOCgt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOCgt2.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PencEOCgt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOCgt2.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PencEOCgt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K23) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K14l K14r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PencEOCgth0 := BndP_Es_004S8.LibSegEs_encEOCgth0.
Definition KS_encEOCgth0 : list nat := Eval vm_compute in (BG.kept_list 60 PencEOCgth0.regs0 PencEOCgth0.regs_out0).
Lemma KS_encEOCgth0_ok : BG.kept_ok 60 PencEOCgth0.regs0 PencEOCgth0.regs_out0 KS_encEOCgth0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma encEOCgth0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 24) (V 33%nat) -> 4096 <= (V 33%nat) <= 140737488355328 ->
  aligned (V 33%nat) 8 -> L5.u32_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 48) (V 36%nat) -> 1 <= (V 36%nat) <= 1025 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 32) (V 34%nat) ->
  4120 <= (V 34%nat) <= 140737488355328 -> aligned (V 34%nat) 8 -> 24 <= ((V 34%nat) - (V 33%nat)) <= 100000 -> L5.u32_at RSEGS M ((V 34%nat) - 24) 0 ->
  L5.u64_at RSEGS M ((V 34%nat) - 16) (V 38%nat) -> 0 <= (V 38%nat) <= 16777216 -> (((V 34%nat) - 48) + 48 <= ((V 2%nat) - 48) \/ ((V 2%nat) - 48) + 48 <= ((V 34%nat) - 48)) -> (((V 34%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 34%nat) - 48)) ->
  L5.u64_at RSEGS M ((V 34%nat) - 8) (V 39%nat) -> 18446744073692774400 <= (V 39%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= i < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x35f30 M) (st fx' R' 0x36f18 M')
        /\ (forall x, In x KS_encEOCgth0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 221128
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 10) = getr R (reg 12)
        /\ getr R' (reg 11) = Z_to_bv 64 8
        /\ getr R' (reg 13) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 39%nat)
        /\ L5.u32_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 48) ((V 36%nat) - 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 pvzI8 K1 K2 pvzI9 K4 K5 K6 K7 pvzI10 K9 K10 pvzI11 K12 K13 pvzI12 K15 pvzI13 K17 pvzI14 K19 K20 pvzI15 K22 K23 K24 pvzI16.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV39l; move HV39l before pvzI6; pose proof (proj2 pvzI6) as HV39r; move HV39r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV41l; move HV41l before pvzI7; pose proof (proj2 pvzI7) as HV41r; move HV41r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K8l; move K8l before pvzI10; pose proof (proj2 pvzI10) as K8r; move K8r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K11l; move K11l before pvzI11; pose proof (proj2 pvzI11) as K11r; move K11r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K14l; move K14l before pvzI12; pose proof (proj2 pvzI12) as K14r; move K14r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K16l; move K16l before pvzI13; pose proof (proj2 pvzI13) as K16r; move K16r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K18l; move K18l before pvzI14; pose proof (proj2 pvzI14) as K18r; move K18r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K21l; move K21l before pvzI15; pose proof (proj2 pvzI15) as K21r; move K21r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K25l; move K25l before pvzI16; pose proof (proj2 pvzI16) as K25r; move K25r before pvzI16; clear pvzI16.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_41 := V 41%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 41%nat => Z_to_bv 64 vz_41 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 38%nat => vz_38 | 39%nat => vz_39 | 41%nat => vz_41 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E PencEOCgth0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PencEOCgth0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PencEOCgth0.kn0).
  { unfold know_ok, PencEOCgth0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K22; lia | clear - HV2l HV2r K0l K0r K6 K22; lia | clear - HV2l HV2r K0l K0r K6 K22; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r HV34l HV34r K16l K16r K22 K23) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear - HV38l HV38r K21l K21r) | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear - HV39l HV39r K25l K25r) | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PencEOCgth0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PencEOCgth0.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PencEOCgth0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K22 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K6 K23) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K6 K23 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PencEOCgth0.ps0) with 0x36f18 in Hms. change (SR.ps_regs PencEOCgth0.ps0) with (map (fun i => (i, nth i PencEOCgth0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PencEOCgth0.ps0) with PencEOCgth0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PencEOCgth0.regs0 PencEOCgth0.regs_out0 60 KS_encEOCgth0 KS_encEOCgth0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PencEOCgth0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PencEOCgth0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOCgth0.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PencEOCgth0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOCgth0.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PencEOCgth0.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PencEOCgth0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PencEOCgth0.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PencEOCgth0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PencEOCgth0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOCgth0.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PencEOCgth0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOCgth0.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PencEOCgth0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K23) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K14l K14r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PencEOCgth2 := BndP_Es_004S8.LibSegEs_encEOCgth2.
Definition KS_encEOCgth2 : list nat := Eval vm_compute in (BG.kept_list 60 PencEOCgth2.regs0 PencEOCgth2.regs_out0).
Lemma KS_encEOCgth2_ok : BG.kept_ok 60 PencEOCgth2.regs0 PencEOCgth2.regs_out0 KS_encEOCgth2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma encEOCgth2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 24) (V 33%nat) -> 4096 <= (V 33%nat) <= 140737488355328 ->
  aligned (V 33%nat) 8 -> L5.u32_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 48) (V 36%nat) -> 1 <= (V 36%nat) <= 1025 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 32) (V 34%nat) ->
  4120 <= (V 34%nat) <= 140737488355328 -> aligned (V 34%nat) 8 -> 24 <= ((V 34%nat) - (V 33%nat)) <= 100000 -> L5.u32_at RSEGS M ((V 34%nat) - 24) 2 ->
  L5.u64_at RSEGS M ((V 34%nat) - 16) (V 38%nat) -> 0 <= (V 38%nat) <= 16777216 -> (((V 34%nat) - 48) + 48 <= ((V 2%nat) - 48) \/ ((V 2%nat) - 48) + 48 <= ((V 34%nat) - 48)) -> (((V 34%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 34%nat) - 48)) ->
  L5.u64_at RSEGS M ((V 34%nat) - 8) (V 39%nat) -> 18446744073692774400 <= (V 39%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= i < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x35f30 M) (st fx' R' 0x36f18 M')
        /\ (forall x, In x KS_encEOCgth2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 221128
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 10) = getr R (reg 12)
        /\ getr R' (reg 11) = Z_to_bv 64 8
        /\ getr R' (reg 13) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 39%nat)
        /\ L5.u32_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 48) ((V 36%nat) - 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 pvzI8 K1 K2 pvzI9 K4 K5 K6 K7 pvzI10 K9 K10 pvzI11 K12 K13 pvzI12 K15 pvzI13 K17 pvzI14 K19 K20 pvzI15 K22 K23 K24 pvzI16.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV39l; move HV39l before pvzI6; pose proof (proj2 pvzI6) as HV39r; move HV39r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV41l; move HV41l before pvzI7; pose proof (proj2 pvzI7) as HV41r; move HV41r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K8l; move K8l before pvzI10; pose proof (proj2 pvzI10) as K8r; move K8r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K11l; move K11l before pvzI11; pose proof (proj2 pvzI11) as K11r; move K11r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K14l; move K14l before pvzI12; pose proof (proj2 pvzI12) as K14r; move K14r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K16l; move K16l before pvzI13; pose proof (proj2 pvzI13) as K16r; move K16r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K18l; move K18l before pvzI14; pose proof (proj2 pvzI14) as K18r; move K18r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K21l; move K21l before pvzI15; pose proof (proj2 pvzI15) as K21r; move K21r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K25l; move K25l before pvzI16; pose proof (proj2 pvzI16) as K25r; move K25r before pvzI16; clear pvzI16.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_41 := V 41%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 41%nat => Z_to_bv 64 vz_41 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 38%nat => vz_38 | 39%nat => vz_39 | 41%nat => vz_41 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E PencEOCgth2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PencEOCgth2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PencEOCgth2.kn0).
  { unfold know_ok, PencEOCgth2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K22; lia | clear - HV2l HV2r K0l K0r K6 K22; lia | clear - HV2l HV2r K0l K0r K6 K22; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r HV34l HV34r K16l K16r K22 K23) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear - HV38l HV38r K21l K21r) | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear - HV39l HV39r K25l K25r) | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PencEOCgth2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PencEOCgth2.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PencEOCgth2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K22 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K6 K23) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K6 K23 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PencEOCgth2.ps0) with 0x36f18 in Hms. change (SR.ps_regs PencEOCgth2.ps0) with (map (fun i => (i, nth i PencEOCgth2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PencEOCgth2.ps0) with PencEOCgth2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PencEOCgth2.regs0 PencEOCgth2.regs_out0 60 KS_encEOCgth2 KS_encEOCgth2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PencEOCgth2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PencEOCgth2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOCgth2.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PencEOCgth2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOCgth2.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PencEOCgth2.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PencEOCgth2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PencEOCgth2.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PencEOCgth2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PencEOCgth2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOCgth2.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PencEOCgth2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOCgth2.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PencEOCgth2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K23) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K14l K14r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PencEOClt0 := BndP_Es_004S8.LibSegEs_encEOClt0.
Definition KS_encEOClt0 : list nat := Eval vm_compute in (BG.kept_list 60 PencEOClt0.regs0 PencEOClt0.regs_out0).
Lemma KS_encEOClt0_ok : BG.kept_ok 60 PencEOClt0.regs0 PencEOClt0.regs_out0 KS_encEOClt0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma encEOClt0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 24) (V 33%nat) -> 4096 <= (V 33%nat) <= 140737488355328 ->
  aligned (V 33%nat) 8 -> L5.u32_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 48) (V 36%nat) -> 1 <= (V 36%nat) <= 1025 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 32) (V 34%nat) ->
  4120 <= (V 34%nat) <= 140737488355328 -> aligned (V 34%nat) 8 -> 24 <= ((V 34%nat) - (V 33%nat)) <= 100000 -> L5.u32_at RSEGS M ((V 34%nat) - 24) 0 ->
  L5.u64_at RSEGS M ((V 34%nat) - 16) (V 38%nat) -> 0 <= (V 38%nat) <= 16777216 -> (((V 34%nat) - 48) + 48 <= ((V 2%nat) - 48) \/ ((V 2%nat) - 48) + 48 <= ((V 34%nat) - 48)) -> (((V 34%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 34%nat) - 48)) ->
  L5.u64_at RSEGS M ((V 34%nat) - 8) (V 39%nat) -> 0 <= (V 39%nat) <= 16777215 -> 1 <= ((V 38%nat) - (V 39%nat)) <= 16777216 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= i < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x35f30 M) (st fx' R' 0x36f18 M')
        /\ (forall x, In x KS_encEOClt0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 221128
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 10) = getr R (reg 12)
        /\ getr R' (reg 11) = Z_to_bv 64 9
        /\ getr R' (reg 13) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 39%nat)
        /\ L5.u32_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 48) ((V 36%nat) - 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 pvzI8 K1 K2 pvzI9 K4 K5 K6 K7 pvzI10 K9 K10 pvzI11 K12 K13 pvzI12 K15 pvzI13 K17 pvzI14 K19 K20 pvzI15 K22 K23 K24 pvzI16 pvzI17.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV39l; move HV39l before pvzI6; pose proof (proj2 pvzI6) as HV39r; move HV39r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV41l; move HV41l before pvzI7; pose proof (proj2 pvzI7) as HV41r; move HV41r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K8l; move K8l before pvzI10; pose proof (proj2 pvzI10) as K8r; move K8r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K11l; move K11l before pvzI11; pose proof (proj2 pvzI11) as K11r; move K11r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K14l; move K14l before pvzI12; pose proof (proj2 pvzI12) as K14r; move K14r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K16l; move K16l before pvzI13; pose proof (proj2 pvzI13) as K16r; move K16r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K18l; move K18l before pvzI14; pose proof (proj2 pvzI14) as K18r; move K18r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K21l; move K21l before pvzI15; pose proof (proj2 pvzI15) as K21r; move K21r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K25l; move K25l before pvzI16; pose proof (proj2 pvzI16) as K25r; move K25r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K26l; move K26l before pvzI17; pose proof (proj2 pvzI17) as K26r; move K26r before pvzI17; clear pvzI17.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_41 := V 41%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 41%nat => Z_to_bv 64 vz_41 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 38%nat => vz_38 | 39%nat => vz_39 | 41%nat => vz_41 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E PencEOClt0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PencEOClt0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PencEOClt0.kn0).
  { unfold know_ok, PencEOClt0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K22; lia | clear - HV2l HV2r K0l K0r K6 K22; lia | clear - HV2l HV2r K0l K0r K6 K22; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r HV34l HV34r K16l K16r K22 K23) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear - HV38l HV38r K21l K21r K26l K26r) | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K21l K21r K26l K26r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear - HV39l HV39r K25l K25r K26l K26r) | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K25l K25r K26l K26r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K21l K21r K26l K26r HV39l HV39r K25l K25r) | exact (conj K26l K26r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PencEOClt0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PencEOClt0.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PencEOClt0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K22 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K6 K23) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K6 K23 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PencEOClt0.ps0) with 0x36f18 in Hms. change (SR.ps_regs PencEOClt0.ps0) with (map (fun i => (i, nth i PencEOClt0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PencEOClt0.ps0) with PencEOClt0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PencEOClt0.regs0 PencEOClt0.regs_out0 60 KS_encEOClt0 KS_encEOClt0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PencEOClt0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PencEOClt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOClt0.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PencEOClt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOClt0.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PencEOClt0.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PencEOClt0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PencEOClt0.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PencEOClt0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PencEOClt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOClt0.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PencEOClt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOClt0.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PencEOClt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K23) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K14l K14r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PencEOClt2 := BndP_Es_004S8.LibSegEs_encEOClt2.
Definition KS_encEOClt2 : list nat := Eval vm_compute in (BG.kept_list 60 PencEOClt2.regs0 PencEOClt2.regs_out0).
Lemma KS_encEOClt2_ok : BG.kept_ok 60 PencEOClt2.regs0 PencEOClt2.regs_out0 KS_encEOClt2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma encEOClt2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 24) (V 33%nat) -> 4096 <= (V 33%nat) <= 140737488355328 ->
  aligned (V 33%nat) 8 -> L5.u32_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 48) (V 36%nat) -> 1 <= (V 36%nat) <= 1025 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 32) (V 34%nat) ->
  4120 <= (V 34%nat) <= 140737488355328 -> aligned (V 34%nat) 8 -> 24 <= ((V 34%nat) - (V 33%nat)) <= 100000 -> L5.u32_at RSEGS M ((V 34%nat) - 24) 2 ->
  L5.u64_at RSEGS M ((V 34%nat) - 16) (V 38%nat) -> 0 <= (V 38%nat) <= 16777216 -> (((V 34%nat) - 48) + 48 <= ((V 2%nat) - 48) \/ ((V 2%nat) - 48) + 48 <= ((V 34%nat) - 48)) -> (((V 34%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 34%nat) - 48)) ->
  L5.u64_at RSEGS M ((V 34%nat) - 8) (V 39%nat) -> 0 <= (V 39%nat) <= 16777215 -> 1 <= ((V 38%nat) - (V 39%nat)) <= 16777216 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= i < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x35f30 M) (st fx' R' 0x36f18 M')
        /\ (forall x, In x KS_encEOClt2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 221128
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 10) = getr R (reg 12)
        /\ getr R' (reg 11) = Z_to_bv 64 9
        /\ getr R' (reg 13) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 39%nat)
        /\ L5.u32_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 48) ((V 36%nat) - 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 pvzI8 K1 K2 pvzI9 K4 K5 K6 K7 pvzI10 K9 K10 pvzI11 K12 K13 pvzI12 K15 pvzI13 K17 pvzI14 K19 K20 pvzI15 K22 K23 K24 pvzI16 pvzI17.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV39l; move HV39l before pvzI6; pose proof (proj2 pvzI6) as HV39r; move HV39r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV41l; move HV41l before pvzI7; pose proof (proj2 pvzI7) as HV41r; move HV41r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K8l; move K8l before pvzI10; pose proof (proj2 pvzI10) as K8r; move K8r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K11l; move K11l before pvzI11; pose proof (proj2 pvzI11) as K11r; move K11r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K14l; move K14l before pvzI12; pose proof (proj2 pvzI12) as K14r; move K14r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K16l; move K16l before pvzI13; pose proof (proj2 pvzI13) as K16r; move K16r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K18l; move K18l before pvzI14; pose proof (proj2 pvzI14) as K18r; move K18r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K21l; move K21l before pvzI15; pose proof (proj2 pvzI15) as K21r; move K21r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K25l; move K25l before pvzI16; pose proof (proj2 pvzI16) as K25r; move K25r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K26l; move K26l before pvzI17; pose proof (proj2 pvzI17) as K26r; move K26r before pvzI17; clear pvzI17.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_41 := V 41%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 41%nat => Z_to_bv 64 vz_41 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 38%nat => vz_38 | 39%nat => vz_39 | 41%nat => vz_41 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E PencEOClt2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PencEOClt2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PencEOClt2.kn0).
  { unfold know_ok, PencEOClt2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K22; lia | clear - HV2l HV2r K0l K0r K6 K22; lia | clear - HV2l HV2r K0l K0r K6 K22; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | clear - K3l K3r K6 K23; lia | clear - K3l K3r K6 K23; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r HV34l HV34r K16l K16r K22 K23) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear - HV38l HV38r K21l K21r K26l K26r) | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K21l K21r K26l K26r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K23) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K22 K23) | evalEk ZA ltac:(clear - HV39l HV39r K25l K25r K26l K26r) | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | clear - HV34l HV34r K16l K16r K18l K18r K22 K23; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K25l K25r K26l K26r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K21l K21r K26l K26r HV39l HV39r K25l K25r) | exact (conj K26l K26r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PencEOClt2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PencEOClt2.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PencEOClt2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K22 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K6 K23) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K6 K23 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PencEOClt2.ps0) with 0x36f18 in Hms. change (SR.ps_regs PencEOClt2.ps0) with (map (fun i => (i, nth i PencEOClt2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PencEOClt2.ps0) with PencEOClt2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PencEOClt2.regs0 PencEOClt2.regs_out0 60 KS_encEOClt2 KS_encEOClt2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PencEOClt2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PencEOClt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOClt2.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PencEOClt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOClt2.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PencEOClt2.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PencEOClt2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PencEOClt2.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PencEOClt2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PencEOClt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOClt2.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PencEOClt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOClt2.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PencEOClt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K23) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K14l K14r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PencEOI1 := BndP_Es_005S8.LibSegEs_encEOI1.
Definition KS_encEOI1 : list nat := Eval vm_compute in (BG.kept_list 60 PencEOI1.regs0 PencEOI1.regs_out0).
Lemma KS_encEOI1_ok : BG.kept_ok 60 PencEOI1.regs0 PencEOI1.regs_out0 KS_encEOI1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma encEOI1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 24) (V 33%nat) -> 4096 <= (V 33%nat) <= 140737488355328 ->
  aligned (V 33%nat) 8 -> L5.u32_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 48) (V 36%nat) -> 1 <= (V 36%nat) <= 1025 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 32) (V 34%nat) ->
  4120 <= (V 34%nat) <= 140737488355328 -> aligned (V 34%nat) 8 -> 24 <= ((V 34%nat) - (V 33%nat)) <= 100000 -> L5.u32_at RSEGS M ((V 34%nat) - 24) 1 ->
  L5.u64_at RSEGS M ((V 34%nat) - 16) (V 38%nat) -> L5.u64_at RSEGS M ((V 34%nat) - 8) (V 39%nat) -> 0 <= (V 38%nat) <= 16777216 -> 0 <= (V 39%nat) <= 18446744073709551615 ->
  (((V 34%nat) - 48) + 48 <= ((V 2%nat) - 48) \/ ((V 2%nat) - 48) + 48 <= ((V 34%nat) - 48)) -> (((V 34%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 34%nat) - 48)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= i < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x35f30 M) (st fx' R' 0x372d8 M')
        /\ (forall x, In x KS_encEOI1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 221056
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 13) = Z_to_bv 64 1
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 48) 125
        /\ L5.u32_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 48) ((V 36%nat) - 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 pvzI8 K1 K2 pvzI9 K4 K5 K6 K7 pvzI10 K9 K10 pvzI11 K12 K13 pvzI12 K15 pvzI13 K17 pvzI14 K19 K20 K21 pvzI15 pvzI16 K24 K25.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV39l; move HV39l before pvzI6; pose proof (proj2 pvzI6) as HV39r; move HV39r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV41l; move HV41l before pvzI7; pose proof (proj2 pvzI7) as HV41r; move HV41r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K8l; move K8l before pvzI10; pose proof (proj2 pvzI10) as K8r; move K8r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K11l; move K11l before pvzI11; pose proof (proj2 pvzI11) as K11r; move K11r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K14l; move K14l before pvzI12; pose proof (proj2 pvzI12) as K14r; move K14r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K16l; move K16l before pvzI13; pose proof (proj2 pvzI13) as K16r; move K16r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K18l; move K18l before pvzI14; pose proof (proj2 pvzI14) as K18r; move K18r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K22l; move K22l before pvzI15; pose proof (proj2 pvzI15) as K22r; move K22r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K23l; move K23l before pvzI16; pose proof (proj2 pvzI16) as K23r; move K23r before pvzI16; clear pvzI16.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_41 := V 41%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 41%nat => Z_to_bv 64 vz_41 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 38%nat => vz_38 | 39%nat => vz_39 | 41%nat => vz_41 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E PencEOI1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PencEOI1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PencEOI1.kn0).
  { unfold know_ok, PencEOI1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K24; lia | clear - HV2l HV2r K0l K0r K6 K24; lia | clear - HV2l HV2r K0l K0r K6 K24; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K3l K3r K6 K25) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K3l K3r K6 K25) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K3l K3r K6 K25) | evalEk ZA ltac:(clear) | clear - K3l K3r K6 K25; lia | clear - K3l K3r K6 K25; lia | clear - K3l K3r K6 K25; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K25) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K25) | evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear - K3l K3r K6 K25; lia | clear - K3l K3r K6 K25; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K25) | evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear - K3l K3r K6 K25; lia | clear - K3l K3r K6 K25; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - K3l K3r K6 K25) | evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | clear - K3l K3r K6 K25; lia | clear - K3l K3r K6 K25; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K25) | evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K24 K25) | clear - K3l K3r K6 K25; lia | clear - K3l K3r K6 K25; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K24 K25) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K24 K25) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r HV34l HV34r K16l K16r K24 K25) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K24 K25) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K16l K16r K18l K18r K24 K25; lia | clear - HV34l HV34r K16l K16r K18l K18r K24 K25; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K24 K25) | evalEk ZA ltac:(clear - HV38l HV38r K22l K22r) | clear - HV34l HV34r K16l K16r K18l K18r K24 K25; lia | clear - HV34l HV34r K16l K16r K18l K18r K24 K25; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K24 K25) | evalEk ZA ltac:(clear - HV39l HV39r K23l K23r) | clear - HV34l HV34r K16l K16r K18l K18r K24 K25; lia | clear - HV34l HV34r K16l K16r K18l K18r K24 K25; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K24 K25) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K24 K25) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K25) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PencEOI1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PencEOI1.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PencEOI1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K24 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K6 K25) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K6 K25 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PencEOI1.ps0) with 0x372d8 in Hms. change (SR.ps_regs PencEOI1.ps0) with (map (fun i => (i, nth i PencEOI1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PencEOI1.ps0) with PencEOI1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PencEOI1.regs0 PencEOI1.regs_out0 60 KS_encEOI1 KS_encEOI1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PencEOI1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PencEOI1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOI1.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PencEOI1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOI1.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PencEOI1.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PencEOI1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PencEOI1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOI1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PencEOI1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOI1.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PencEOI1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOI1.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PencEOI1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K25) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K14l K14r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PencEOI3 := BndP_Es_005S8.LibSegEs_encEOI3.
Definition KS_encEOI3 : list nat := Eval vm_compute in (BG.kept_list 60 PencEOI3.regs0 PencEOI3.regs_out0).
Lemma KS_encEOI3_ok : BG.kept_ok 60 PencEOI3.regs0 PencEOI3.regs_out0 KS_encEOI3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma encEOI3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 24) (V 33%nat) -> 4096 <= (V 33%nat) <= 140737488355328 ->
  aligned (V 33%nat) 8 -> L5.u32_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 48) (V 36%nat) -> 1 <= (V 36%nat) <= 1025 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 32) (V 34%nat) ->
  4120 <= (V 34%nat) <= 140737488355328 -> aligned (V 34%nat) 8 -> 24 <= ((V 34%nat) - (V 33%nat)) <= 100000 -> L5.u32_at RSEGS M ((V 34%nat) - 24) 3 ->
  L5.u64_at RSEGS M ((V 34%nat) - 16) (V 38%nat) -> L5.u64_at RSEGS M ((V 34%nat) - 8) (V 39%nat) -> 0 <= (V 38%nat) <= 16777216 -> 0 <= (V 39%nat) <= 18446744073709551615 ->
  (((V 34%nat) - 48) + 48 <= ((V 2%nat) - 48) \/ ((V 2%nat) - 48) + 48 <= ((V 34%nat) - 48)) -> (((V 34%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 34%nat) - 48)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= i < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x35f30 M) (st fx' R' 0x372d8 M')
        /\ (forall x, In x KS_encEOI3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 221056
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 13) = Z_to_bv 64 1
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 48) 125
        /\ L5.u32_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 48) ((V 36%nat) - 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 pvzI8 K1 K2 pvzI9 K4 K5 K6 K7 pvzI10 K9 K10 pvzI11 K12 K13 pvzI12 K15 pvzI13 K17 pvzI14 K19 K20 K21 pvzI15 pvzI16 K24 K25.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV39l; move HV39l before pvzI6; pose proof (proj2 pvzI6) as HV39r; move HV39r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV41l; move HV41l before pvzI7; pose proof (proj2 pvzI7) as HV41r; move HV41r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K8l; move K8l before pvzI10; pose proof (proj2 pvzI10) as K8r; move K8r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K11l; move K11l before pvzI11; pose proof (proj2 pvzI11) as K11r; move K11r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K14l; move K14l before pvzI12; pose proof (proj2 pvzI12) as K14r; move K14r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K16l; move K16l before pvzI13; pose proof (proj2 pvzI13) as K16r; move K16r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K18l; move K18l before pvzI14; pose proof (proj2 pvzI14) as K18r; move K18r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K22l; move K22l before pvzI15; pose proof (proj2 pvzI15) as K22r; move K22r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K23l; move K23l before pvzI16; pose proof (proj2 pvzI16) as K23r; move K23r before pvzI16; clear pvzI16.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_41 := V 41%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 41%nat => Z_to_bv 64 vz_41 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 38%nat => vz_38 | 39%nat => vz_39 | 41%nat => vz_41 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E PencEOI3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PencEOI3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PencEOI3.kn0).
  { unfold know_ok, PencEOI3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K24; lia | clear - HV2l HV2r K0l K0r K6 K24; lia | clear - HV2l HV2r K0l K0r K6 K24; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K3l K3r K6 K25) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K3l K3r K6 K25) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K3l K3r K6 K25) | evalEk ZA ltac:(clear) | clear - K3l K3r K6 K25; lia | clear - K3l K3r K6 K25; lia | clear - K3l K3r K6 K25; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K25) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K25) | evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear - K3l K3r K6 K25; lia | clear - K3l K3r K6 K25; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K25) | evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear - K3l K3r K6 K25; lia | clear - K3l K3r K6 K25; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - K3l K3r K6 K25) | evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | clear - K3l K3r K6 K25; lia | clear - K3l K3r K6 K25; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K25) | evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K24 K25) | clear - K3l K3r K6 K25; lia | clear - K3l K3r K6 K25; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K24 K25) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K24 K25) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K18l K18r HV34l HV34r K16l K16r K24 K25) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K24 K25) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K16l K16r K18l K18r K24 K25; lia | clear - HV34l HV34r K16l K16r K18l K18r K24 K25; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K24 K25) | evalEk ZA ltac:(clear - HV38l HV38r K22l K22r) | clear - HV34l HV34r K16l K16r K18l K18r K24 K25; lia | clear - HV34l HV34r K16l K16r K18l K18r K24 K25; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K24 K25) | evalEk ZA ltac:(clear - HV39l HV39r K23l K23r) | clear - HV34l HV34r K16l K16r K18l K18r K24 K25; lia | clear - HV34l HV34r K16l K16r K18l K18r K24 K25; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K24 K25) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18l K18r K24 K25) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K25) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PencEOI3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PencEOI3.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PencEOI3.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K24 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K6 K25) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K6 K25 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PencEOI3.ps0) with 0x372d8 in Hms. change (SR.ps_regs PencEOI3.ps0) with (map (fun i => (i, nth i PencEOI3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PencEOI3.ps0) with PencEOI3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PencEOI3.regs0 PencEOI3.regs_out0 60 KS_encEOI3 KS_encEOI3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PencEOI3.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PencEOI3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOI3.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PencEOI3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOI3.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PencEOI3.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PencEOI3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PencEOI3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOI3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PencEOI3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOI3.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PencEOI3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOI3.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PencEOI3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K25) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K14l K14r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PencEOJ1 := BndP_Es_005S8.LibSegEs_encEOJ1.
Definition KS_encEOJ1 : list nat := Eval vm_compute in (BG.kept_list 60 PencEOJ1.regs0 PencEOJ1.regs_out0).
Lemma KS_encEOJ1_ok : BG.kept_ok 60 PencEOJ1.regs0 PencEOJ1.regs_out0 KS_encEOJ1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma encEOJ1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 56 -> (((V 2%nat) - 48) + 48 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((V 10%nat) + 24) (V 33%nat) ->
  4096 <= (V 33%nat) <= 140737488355328 -> aligned (V 33%nat) 8 -> L5.u64_at RSEGS M ((V 10%nat) + 32) ((V 33%nat) + 24) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 10%nat) + 32) <= bv_unsigned a < ((V 10%nat) + 32) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 10%nat) + 32) <= i < ((V 10%nat) + 32) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x35f80 M) (st fx' R' 0x35fdc M')
        /\ (forall x, In x KS_encEOJ1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 10%nat) + 32) (V 33%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G10 pvzI8 K1 K2 pvzI9 K4 K5 K6 K7 pvzI10 K9 K10 K11 K12 K13.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV44l; move HV44l before pvzI4; pose proof (proj2 pvzI4) as HV44r; move HV44r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV45l; move HV45l before pvzI5; pose proof (proj2 pvzI5) as HV45r; move HV45r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV46l; move HV46l before pvzI6; pose proof (proj2 pvzI6) as HV46r; move HV46r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV55l; move HV55l before pvzI7; pose proof (proj2 pvzI7) as HV55r; move HV55r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K8l; move K8l before pvzI10; pose proof (proj2 pvzI10) as K8r; move K8r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_55 := V 55%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 33%nat => Z_to_bv 64 vz_33 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 55%nat => Z_to_bv 64 vz_55 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 33%nat => vz_33 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 55%nat => vz_55 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 56%nat. }
  assert (HR: regs_ok E PencEOJ1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PencEOJ1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PencEOJ1.kn0).
  { unfold know_ok, PencEOJ1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r) | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r) | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K13]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PencEOJ1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PencEOJ1.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_10 + 32) <= bv_unsigned a < (vz_10 + 32) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PencEOJ1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk' ZA Hag ltac:(clear) | clear - HV10l HV10r K3l K3r K6 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PencEOJ1.ps0) with 0x35fdc in Hms. change (SR.ps_regs PencEOJ1.ps0) with (map (fun i => (i, nth i PencEOJ1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PencEOJ1.ps0) with PencEOJ1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PencEOJ1.regs0 PencEOJ1.regs_out0 60 KS_encEOJ1 KS_encEOJ1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PencEOJ1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PencEOJ1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOJ1.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PencEOJ1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOJ1.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PencEOJ1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOJ1.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PencEOJ1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOJ1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PencEOJ1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOJ1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PencEOJ1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOJ1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PencEOJ1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r) | clear; lia].
Qed.

Module PencEOJ2 := BndP_Es_005S8.LibSegEs_encEOJ2.
Definition KS_encEOJ2 : list nat := Eval vm_compute in (BG.kept_list 60 PencEOJ2.regs0 PencEOJ2.regs_out0).
Lemma KS_encEOJ2_ok : BG.kept_ok 60 PencEOJ2.regs0 PencEOJ2.regs_out0 KS_encEOJ2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma encEOJ2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 56 -> (((V 2%nat) - 48) + 48 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((V 10%nat) + 24) (V 33%nat) ->
  4096 <= (V 33%nat) <= 140737488355328 -> aligned (V 33%nat) 8 -> L5.u64_at RSEGS M ((V 10%nat) + 32) (V 34%nat) -> 4144 <= (V 34%nat) <= 140737488355328 ->
  aligned (V 34%nat) 8 -> 48 <= ((V 34%nat) - (V 33%nat)) <= 100000 -> L5.writable RSEGS M ((V 34%nat) - 48) 48 -> (((V 34%nat) - 48) + 48 <= ((V 2%nat) - 48) \/ ((V 2%nat) - 48) + 48 <= ((V 34%nat) - 48)) ->
  (((V 34%nat) - 48) + 48 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 34%nat) - 48)) -> L5.u64_at RSEGS M ((V 34%nat) - 32) (V 42%nat) -> 0 <= (V 42%nat) <= 18446744073709551614 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 10%nat) + 32) <= bv_unsigned a < ((V 10%nat) + 32) + 8) -> ~ (((V 34%nat) - 32) <= bv_unsigned a < ((V 34%nat) - 32) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 10%nat) + 32) <= i < ((V 10%nat) + 32) + 8) -> ~ (((V 34%nat) - 32) <= i < ((V 34%nat) - 32) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x35f80 M) (st fx' R' 0x35fdc M')
        /\ (forall x, In x KS_encEOJ2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 42%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 34%nat) - 24)
        /\ L5.u64_at RSEGS M' ((V 34%nat) - 32) ((V 42%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 10%nat) + 32) ((V 34%nat) - 24)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G8 G10 pvzI10 K1 K2 pvzI11 K4 K5 K6 K7 pvzI12 K9 K10 pvzI13 K12 pvzI14 K14 K15 K16 K17 pvzI15 K19 K20 K21.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV42l; move HV42l before pvzI5; pose proof (proj2 pvzI5) as HV42r; move HV42r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV44l; move HV44l before pvzI6; pose proof (proj2 pvzI6) as HV44r; move HV44r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV45l; move HV45l before pvzI7; pose proof (proj2 pvzI7) as HV45r; move HV45r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV46l; move HV46l before pvzI8; pose proof (proj2 pvzI8) as HV46r; move HV46r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV55l; move HV55l before pvzI9; pose proof (proj2 pvzI9) as HV55r; move HV55r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K0l; move K0l before pvzI10; pose proof (proj2 pvzI10) as K0r; move K0r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K3l; move K3l before pvzI11; pose proof (proj2 pvzI11) as K3r; move K3r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K8l; move K8l before pvzI12; pose proof (proj2 pvzI12) as K8r; move K8r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K11l; move K11l before pvzI13; pose proof (proj2 pvzI13) as K11r; move K11r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K13l; move K13l before pvzI14; pose proof (proj2 pvzI14) as K13r; move K13r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K18l; move K18l before pvzI15; pose proof (proj2 pvzI15) as K18r; move K18r before pvzI15; clear pvzI15.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_55 := V 55%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 42%nat => Z_to_bv 64 vz_42 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 55%nat => Z_to_bv 64 vz_55 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 33%nat => vz_33 | 34%nat => vz_34 | 42%nat => vz_42 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 55%nat => vz_55 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 56%nat. }
  assert (HR: regs_ok E PencEOJ2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PencEOJ2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PencEOJ2.kn0).
  { unfold know_ok, PencEOJ2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K15) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K15) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K15) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K15; lia | clear - HV2l HV2r K0l K0r K6 K15; lia | clear - HV2l HV2r K0l K0r K6 K15; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K16) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K16) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K16) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K3l K3r K6 K16; lia | clear - HV10l HV10r K3l K3r K6 K16; lia | clear - HV10l HV10r K3l K3r K6 K16; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K16) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K16) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K13l K13r) | clear - HV10l HV10r K3l K3r K6 K16; lia | clear - HV10l HV10r K3l K3r K6 K16; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K13l K13r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K13l K13r) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K16) | evalEk ZA ltac:(clear - HV34l HV34r K11l K11r K13l K13r K15 K16) | clear - HV10l HV10r K3l K3r K6 K16; lia | clear - HV10l HV10r K3l K3r K6 K16; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K11l K11r K13l K13r K15 K16) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K11l K11r K13l K13r K15 K16) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K13l K13r HV34l HV34r K11l K11r K15 K16) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV34l HV34r K11l K11r K13l K13r K15 K16) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K11l K11r K13l K13r K15 K16; lia | clear - HV34l HV34r K11l K11r K13l K13r K15 K16; lia | clear - HV34l HV34r K11l K11r K13l K13r K15 K16; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K11l K11r K13l K13r K15 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K15) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K11l K11r K13l K13r K15 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K16) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K11l K11r K13l K13r K15 K16) | evalEk ZA ltac:(clear - HV42l HV42r K18l K18r) | clear - HV34l HV34r K11l K11r K13l K13r K15 K16; lia | clear - HV34l HV34r K11l K11r K13l K13r K15 K16; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K18l K18r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K15) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K6 K15; lia | clear - HV2l HV2r K0l K0r K6 K15; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K15) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K6 K15; lia | clear - HV2l HV2r K0l K0r K6 K15; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K15) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K6 K15; lia | clear - HV2l HV2r K0l K0r K6 K15; lia | exactA K21]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PencEOJ2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PencEOJ2.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_10 + 32) <= bv_unsigned a < (vz_10 + 32) + 8) -> ~ ((vz_34 - 32) <= bv_unsigned a < (vz_34 - 32) + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PencEOJ2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6 K16) | evalEk' ZA Hag ltac:(clear) | clear - HV10l HV10r K3l K3r K6 K16 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV34l HV34r K11l K11r K13l K13r K15 K16) | evalEk' ZA Hag ltac:(clear) | clear - HV34l HV34r K11l K11r K13l K13r K15 K16 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PencEOJ2.ps0) with 0x35fdc in Hms. change (SR.ps_regs PencEOJ2.ps0) with (map (fun i => (i, nth i PencEOJ2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PencEOJ2.ps0) with PencEOJ2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PencEOJ2.regs0 PencEOJ2.regs_out0 60 KS_encEOJ2 KS_encEOJ2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PencEOJ2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PencEOJ2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOJ2.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PencEOJ2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOJ2.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PencEOJ2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOJ2.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PencEOJ2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOJ2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PencEOJ2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOJ2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PencEOJ2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOJ2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PencEOJ2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV34l HV34r K11l K11r K13l K13r K15 K16) | evalEk' ZA Hag ltac:(clear - HV42l HV42r K18l K18r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6 K16) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K11l K11r K13l K13r K15 K16) | clear; lia].
Qed.

Module PencEOJ2w := BndP_Es_005S8.LibSegEs_encEOJ2w.
Definition KS_encEOJ2w : list nat := Eval vm_compute in (BG.kept_list 60 PencEOJ2w.regs0 PencEOJ2w.regs_out0).
Lemma KS_encEOJ2w_ok : BG.kept_ok 60 PencEOJ2w.regs0 PencEOJ2w.regs_out0 KS_encEOJ2w = true. Proof. vm_compute. reflexivity. Qed.
Lemma encEOJ2w_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 56 -> (((V 2%nat) - 48) + 48 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((V 10%nat) + 24) (V 33%nat) ->
  4096 <= (V 33%nat) <= 140737488355328 -> aligned (V 33%nat) 8 -> L5.u64_at RSEGS M ((V 10%nat) + 32) (V 34%nat) -> 4144 <= (V 34%nat) <= 140737488355328 ->
  aligned (V 34%nat) 8 -> 48 <= ((V 34%nat) - (V 33%nat)) <= 100000 -> L5.writable RSEGS M ((V 34%nat) - 48) 48 -> (((V 34%nat) - 48) + 48 <= ((V 2%nat) - 48) \/ ((V 2%nat) - 48) + 48 <= ((V 34%nat) - 48)) ->
  (((V 34%nat) - 48) + 48 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 34%nat) - 48)) -> L5.u64_at RSEGS M ((V 34%nat) - 32) 18446744073709551615 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 10%nat) + 32) <= bv_unsigned a < ((V 10%nat) + 32) + 8) -> ~ (((V 34%nat) - 32) <= bv_unsigned a < ((V 34%nat) - 32) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 10%nat) + 32) <= i < ((V 10%nat) + 32) + 8) -> ~ (((V 34%nat) - 32) <= i < ((V 34%nat) - 32) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x35f80 M) (st fx' R' 0x35fdc M')
        /\ (forall x, In x KS_encEOJ2w -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 34%nat) - 24)
        /\ L5.u64_at RSEGS M' ((V 34%nat) - 32) 0
        /\ L5.u64_at RSEGS M' ((V 10%nat) + 32) ((V 34%nat) - 24)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G10 pvzI9 K1 K2 pvzI10 K4 K5 K6 K7 pvzI11 K9 K10 pvzI12 K12 pvzI13 K14 K15 K16 K17 K18 K19 K20.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV44l; move HV44l before pvzI5; pose proof (proj2 pvzI5) as HV44r; move HV44r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV45l; move HV45l before pvzI6; pose proof (proj2 pvzI6) as HV45r; move HV45r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV46l; move HV46l before pvzI7; pose proof (proj2 pvzI7) as HV46r; move HV46r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV55l; move HV55l before pvzI8; pose proof (proj2 pvzI8) as HV55r; move HV55r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K0l; move K0l before pvzI9; pose proof (proj2 pvzI9) as K0r; move K0r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K8l; move K8l before pvzI11; pose proof (proj2 pvzI11) as K8r; move K8r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K11l; move K11l before pvzI12; pose proof (proj2 pvzI12) as K11r; move K11r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K13l; move K13l before pvzI13; pose proof (proj2 pvzI13) as K13r; move K13r before pvzI13; clear pvzI13.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_55 := V 55%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 55%nat => Z_to_bv 64 vz_55 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 33%nat => vz_33 | 34%nat => vz_34 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 55%nat => vz_55 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 56%nat. }
  assert (HR: regs_ok E PencEOJ2w.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PencEOJ2w.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PencEOJ2w.kn0).
  { unfold know_ok, PencEOJ2w.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K15) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K15) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K15) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K15; lia | clear - HV2l HV2r K0l K0r K6 K15; lia | clear - HV2l HV2r K0l K0r K6 K15; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K16) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K16) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K16) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K3l K3r K6 K16; lia | clear - HV10l HV10r K3l K3r K6 K16; lia | clear - HV10l HV10r K3l K3r K6 K16; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K16) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K16) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K13l K13r) | clear - HV10l HV10r K3l K3r K6 K16; lia | clear - HV10l HV10r K3l K3r K6 K16; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K13l K13r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K13l K13r) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K16) | evalEk ZA ltac:(clear - HV34l HV34r K11l K11r K13l K13r K15 K16) | clear - HV10l HV10r K3l K3r K6 K16; lia | clear - HV10l HV10r K3l K3r K6 K16; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K11l K11r K13l K13r K15 K16) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K11l K11r K13l K13r K15 K16) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K13l K13r HV34l HV34r K11l K11r K15 K16) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV34l HV34r K11l K11r K13l K13r K15 K16) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K11l K11r K13l K13r K15 K16; lia | clear - HV34l HV34r K11l K11r K13l K13r K15 K16; lia | clear - HV34l HV34r K11l K11r K13l K13r K15 K16; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K11l K11r K13l K13r K15 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K15) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K11l K11r K13l K13r K15 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K16) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K11l K11r K13l K13r K15 K16) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K11l K11r K13l K13r K15 K16; lia | clear - HV34l HV34r K11l K11r K13l K13r K15 K16; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K15) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K6 K15; lia | clear - HV2l HV2r K0l K0r K6 K15; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K15) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K6 K15; lia | clear - HV2l HV2r K0l K0r K6 K15; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K15) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K6 K15; lia | clear - HV2l HV2r K0l K0r K6 K15; lia | exactA K20]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PencEOJ2w.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PencEOJ2w.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_10 + 32) <= bv_unsigned a < (vz_10 + 32) + 8) -> ~ ((vz_34 - 32) <= bv_unsigned a < (vz_34 - 32) + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PencEOJ2w.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6 K16) | evalEk' ZA Hag ltac:(clear) | clear - HV10l HV10r K3l K3r K6 K16 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV34l HV34r K11l K11r K13l K13r K15 K16) | evalEk' ZA Hag ltac:(clear) | clear - HV34l HV34r K11l K11r K13l K13r K15 K16 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PencEOJ2w.ps0) with 0x35fdc in Hms. change (SR.ps_regs PencEOJ2w.ps0) with (map (fun i => (i, nth i PencEOJ2w.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PencEOJ2w.ps0) with PencEOJ2w.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PencEOJ2w.regs0 PencEOJ2w.regs_out0 60 KS_encEOJ2w KS_encEOJ2w_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PencEOJ2w.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PencEOJ2w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOJ2w.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PencEOJ2w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOJ2w.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PencEOJ2w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOJ2w.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PencEOJ2w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOJ2w.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PencEOJ2w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOJ2w.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PencEOJ2w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOJ2w.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PencEOJ2w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV34l HV34r K11l K11r K13l K13r K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6 K16) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K11l K11r K13l K13r K15 K16) | clear; lia].
Qed.

Module PencEOR := BndP_Es_005S8.LibSegEs_encEOR.
Definition KS_encEOR : list nat := Eval vm_compute in (BG.kept_list 60 PencEOR.regs0 PencEOR.regs_out0).
Lemma KS_encEOR_ok : BG.kept_ok 60 PencEOR.regs0 PencEOR.regs_out0 KS_encEOR = true. Proof. vm_compute. reflexivity. Qed.
Lemma encEOR_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x35fc8 M) (st fx' R' 0x35fdc M')
        /\ (forall x, In x KS_encEOR -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G10 pvzI7 K1 K2 K3 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV44l; move HV44l before pvzI3; pose proof (proj2 pvzI3) as HV44r; move HV44r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV45l; move HV45l before pvzI4; pose proof (proj2 pvzI4) as HV45r; move HV45r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV46l; move HV46l before pvzI5; pose proof (proj2 pvzI5) as HV46r; move HV46r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV55l; move HV55l before pvzI6; pose proof (proj2 pvzI6) as HV55r; move HV55r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_55 := V 55%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 55%nat => Z_to_bv 64 vz_55 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 55%nat => vz_55 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 56%nat. }
  assert (HR: regs_ok E PencEOR.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PencEOR.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PencEOR.kn0).
  { unfold know_ok, PencEOR.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PencEOR.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PencEOR.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PencEOR.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PencEOR.ps0) with 0x35fdc in Hms. change (SR.ps_regs PencEOR.ps0) with (map (fun i => (i, nth i PencEOR.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PencEOR.ps0) with PencEOR.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PencEOR.regs0 PencEOR.regs_out0 60 KS_encEOR KS_encEOR_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PencEOR.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PencEOR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOR.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PencEOR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOR.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PencEOR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PencEOR.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PencEOR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PencEOR.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PencEOR.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

End PESENDP.
