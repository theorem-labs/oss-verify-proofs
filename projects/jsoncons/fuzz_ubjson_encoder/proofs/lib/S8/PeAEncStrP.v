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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.seg Require BndP_Ea_037S8 BndP_Ea_038S8.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEAENCSTP.
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

Module PaqSAh := BndP_Ea_037S8.LibSegEa_aqSAh.
Definition KS_aqSAh : list nat := Eval vm_compute in (BG.kept_list 60 PaqSAh.regs0 PaqSAh.regs_out0).
Lemma KS_aqSAh_ok : BG.kept_ok 60 PaqSAh.regs0 PaqSAh.regs_out0 KS_aqSAh = true. Proof. vm_compute. reflexivity. Qed.
Lemma aqSAh_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  L5.img_clear M 1253376 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487264 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 -> 4096 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 -> aligned (bv_unsigned (getr R (reg 10))) 8 ->
  (2147446784 + 17592186048512 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= 2147446784) -> L5KA.zeros_at M (((bv_unsigned (getr R (reg 10))) / 8) + 2147450880) 7 -> L5KA.zeros_at M ((((bv_unsigned (getr R (reg 10))) + 8) / 8) + 2147450880) 1 -> (((V 2%nat) - 96) + 96 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 96)) ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 2 <= (bv_unsigned (getr R (reg 12))) <= 3 ->
  4096 <= (bv_unsigned (getr R (reg 11))) <= 140737488355312 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 96) <= bv_unsigned a < ((V 2%nat) - 96) + 96) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 96) <= i < ((V 2%nat) - 96) + 96) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac3d8 M) (st fx' R' 0xaf02c M')
        /\ (forall x, In x KS_aqSAh -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 705632
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 96)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 9) = Z_to_bv 64 ((bv_unsigned (getr R (reg 10))) + 8)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 83)
        /\ getr R' (reg 12) = Z_to_bv 64 2
        /\ getr R' (reg 13) = Z_to_bv 64 1317368
        /\ getr R' (reg 18) = getr R (reg 11)
        /\ getr R' (reg 19) = getr R (reg 14)
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ getr R' (reg 22) = Z_to_bv 64 ((((bv_unsigned (getr R (reg 10))) + 8) / 8) + 2147450880)
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 83) 72
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 G2 K0 K1 K2 pvzI3 K4 K5 pvzI4 K7 K8 K9 K10 K11 K12 pvzI5 K14 pvzI6 pvzI7.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV41l; move HV41l before pvzI2; pose proof (proj2 pvzI2) as HV41r; move HV41r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as K3l; move K3l before pvzI3; pose proof (proj2 pvzI3) as K3r; move K3r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K6l; move K6l before pvzI4; pose proof (proj2 pvzI4) as K6r; move K6r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K13l; move K13l before pvzI5; pose proof (proj2 pvzI5) as K13r; move K13r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K15l; move K15l before pvzI6; pose proof (proj2 pvzI6) as K15r; move K15r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K16l; move K16l before pvzI7; pose proof (proj2 pvzI7) as K16r; move K16r before pvzI7; clear pvzI7.
  set (vz_2 := V 2%nat) in *. set (vz_41 := V 41%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 41%nat => Z_to_bv 64 vz_41 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 41%nat => vz_41 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E PaqSAh.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaqSAh.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaqSAh.kn0).
  { unfold know_ok, PaqSAh.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K6l K6r K8 K11) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K6l K6r K8 K11) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - K6l K6r K8 K11; lia | clear - K6l K6r K8 K11; lia | clear - K6l K6r K8 K11; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - K6l K6r K8 K11; lia | clear - K6l K6r K8 K11; lia | clear - K6l K6r K8 K11; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K6l K6r K8 K11) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r) | clear - K6l K6r K8 K11; lia | clear - K6l K6r K8 K11; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r) | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K15l K15r) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaqSAh.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaqSAh.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 96) <= bv_unsigned a < (vz_2 - 96) + 96) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PaqSAh.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K11 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaqSAh.ps0) with 0xaf02c in Hms. change (SR.ps_regs PaqSAh.ps0) with (map (fun i => (i, nth i PaqSAh.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaqSAh.ps0) with PaqSAh.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaqSAh.regs0 PaqSAh.regs_out0 60 KS_aqSAh KS_aqSAh_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaqSAh.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaqSAh.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSAh.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaqSAh.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSAh.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaqSAh.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PaqSAh.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PaqSAh.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSAh.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaqSAh.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSAh.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaqSAh.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSAh.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PaqSAh.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSAh.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PaqSAh.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSAh.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaqSAh.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PaqSAh.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaqSAh.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PaqSAh.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PaqSAh.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSAh.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PaqSAh.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PaqSAs0 := BndP_Ea_037S8.LibSegEa_aqSAs0.
Definition KS_aqSAs0 : list nat := Eval vm_compute in (BG.kept_list 60 PaqSAs0.regs0 PaqSAs0.regs_out0).
Lemma KS_aqSAs0_ok : BG.kept_ok 60 PaqSAs0.regs0 PaqSAs0.regs_out0 KS_aqSAs0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma aqSAs0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  L5.img_clear M 1253376 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487264 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 -> 4096 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 -> aligned (bv_unsigned (getr R (reg 10))) 8 ->
  (2147446784 + 17592186048512 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= 2147446784) -> L5KA.zeros_at M (((bv_unsigned (getr R (reg 10))) / 8) + 2147450880) 7 -> L5KA.zeros_at M ((((bv_unsigned (getr R (reg 10))) + 8) / 8) + 2147450880) 1 -> (((V 2%nat) - 96) + 96 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 96)) ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 0 <= (bv_unsigned (getr R (reg 12))) <= 1 ->
  4096 <= (bv_unsigned (getr R (reg 11))) <= 140737488355312 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 96) <= bv_unsigned a < ((V 2%nat) - 96) + 96) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 96) <= i < ((V 2%nat) - 96) + 96) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac3d8 M) (st fx' R' 0xaf02c M')
        /\ (forall x, In x KS_aqSAs0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 705632
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 96)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 9) = Z_to_bv 64 ((bv_unsigned (getr R (reg 10))) + 8)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 82)
        /\ getr R' (reg 12) = Z_to_bv 64 2
        /\ getr R' (reg 13) = Z_to_bv 64 1317368
        /\ getr R' (reg 18) = getr R (reg 11)
        /\ getr R' (reg 19) = getr R (reg 14)
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ getr R' (reg 22) = Z_to_bv 64 ((((bv_unsigned (getr R (reg 10))) + 8) / 8) + 2147450880)
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 82) 83
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 G2 K0 K1 K2 pvzI3 K4 K5 pvzI4 K7 K8 K9 K10 K11 K12 pvzI5 K14 pvzI6 pvzI7.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV41l; move HV41l before pvzI2; pose proof (proj2 pvzI2) as HV41r; move HV41r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as K3l; move K3l before pvzI3; pose proof (proj2 pvzI3) as K3r; move K3r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K6l; move K6l before pvzI4; pose proof (proj2 pvzI4) as K6r; move K6r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K13l; move K13l before pvzI5; pose proof (proj2 pvzI5) as K13r; move K13r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K15l; move K15l before pvzI6; pose proof (proj2 pvzI6) as K15r; move K15r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K16l; move K16l before pvzI7; pose proof (proj2 pvzI7) as K16r; move K16r before pvzI7; clear pvzI7.
  set (vz_2 := V 2%nat) in *. set (vz_41 := V 41%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 41%nat => Z_to_bv 64 vz_41 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 41%nat => vz_41 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E PaqSAs0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaqSAs0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaqSAs0.kn0).
  { unfold know_ok, PaqSAs0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K6l K6r K8 K11) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K6l K6r K8 K11) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - K6l K6r K8 K11; lia | clear - K6l K6r K8 K11; lia | clear - K6l K6r K8 K11; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - K6l K6r K8 K11; lia | clear - K6l K6r K8 K11; lia | clear - K6l K6r K8 K11; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K6l K6r K8 K11) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r) | clear - K6l K6r K8 K11; lia | clear - K6l K6r K8 K11; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r) | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K15l K15r) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaqSAs0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaqSAs0.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 96) <= bv_unsigned a < (vz_2 - 96) + 96) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PaqSAs0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K11 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaqSAs0.ps0) with 0xaf02c in Hms. change (SR.ps_regs PaqSAs0.ps0) with (map (fun i => (i, nth i PaqSAs0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaqSAs0.ps0) with PaqSAs0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaqSAs0.regs0 PaqSAs0.regs_out0 60 KS_aqSAs0 KS_aqSAs0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaqSAs0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaqSAs0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSAs0.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaqSAs0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSAs0.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaqSAs0.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PaqSAs0.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PaqSAs0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSAs0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaqSAs0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSAs0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaqSAs0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSAs0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PaqSAs0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSAs0.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PaqSAs0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSAs0.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaqSAs0.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PaqSAs0.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaqSAs0.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PaqSAs0.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PaqSAs0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSAs0.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PaqSAs0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PaqSAs4 := BndP_Ea_038S8.LibSegEa_aqSAs4.
Definition KS_aqSAs4 : list nat := Eval vm_compute in (BG.kept_list 60 PaqSAs4.regs0 PaqSAs4.regs_out0).
Lemma KS_aqSAs4_ok : BG.kept_ok 60 PaqSAs4.regs0 PaqSAs4.regs_out0 KS_aqSAs4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma aqSAs4_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  L5.img_clear M 1253376 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487264 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 -> 4096 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 -> aligned (bv_unsigned (getr R (reg 10))) 8 ->
  (2147446784 + 17592186048512 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= 2147446784) -> L5KA.zeros_at M (((bv_unsigned (getr R (reg 10))) / 8) + 2147450880) 7 -> L5KA.zeros_at M ((((bv_unsigned (getr R (reg 10))) + 8) / 8) + 2147450880) 1 -> (((V 2%nat) - 96) + 96 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 96)) ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 4 <= (bv_unsigned (getr R (reg 12))) <= 31 ->
  4096 <= (bv_unsigned (getr R (reg 11))) <= 140737488355312 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 96) <= bv_unsigned a < ((V 2%nat) - 96) + 96) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 96) <= i < ((V 2%nat) - 96) + 96) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac3d8 M) (st fx' R' 0xaf02c M')
        /\ (forall x, In x KS_aqSAs4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 705632
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 96)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 9) = Z_to_bv 64 ((bv_unsigned (getr R (reg 10))) + 8)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 82)
        /\ getr R' (reg 12) = Z_to_bv 64 2
        /\ getr R' (reg 13) = Z_to_bv 64 1317368
        /\ getr R' (reg 18) = getr R (reg 11)
        /\ getr R' (reg 19) = getr R (reg 14)
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ getr R' (reg 22) = Z_to_bv 64 ((((bv_unsigned (getr R (reg 10))) + 8) / 8) + 2147450880)
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 82) 83
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 G2 K0 K1 K2 pvzI3 K4 K5 pvzI4 K7 K8 K9 K10 K11 K12 pvzI5 K14 pvzI6 pvzI7.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV41l; move HV41l before pvzI2; pose proof (proj2 pvzI2) as HV41r; move HV41r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as K3l; move K3l before pvzI3; pose proof (proj2 pvzI3) as K3r; move K3r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K6l; move K6l before pvzI4; pose proof (proj2 pvzI4) as K6r; move K6r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K13l; move K13l before pvzI5; pose proof (proj2 pvzI5) as K13r; move K13r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K15l; move K15l before pvzI6; pose proof (proj2 pvzI6) as K15r; move K15r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K16l; move K16l before pvzI7; pose proof (proj2 pvzI7) as K16r; move K16r before pvzI7; clear pvzI7.
  set (vz_2 := V 2%nat) in *. set (vz_41 := V 41%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 41%nat => Z_to_bv 64 vz_41 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 41%nat => vz_41 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E PaqSAs4.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaqSAs4.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaqSAs4.kn0).
  { unfold know_ok, PaqSAs4.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K6l K6r K8 K11) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K6l K6r K8 K11) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - K6l K6r K8 K11; lia | clear - K6l K6r K8 K11; lia | clear - K6l K6r K8 K11; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - K6l K6r K8 K11; lia | clear - K6l K6r K8 K11; lia | clear - K6l K6r K8 K11; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K6l K6r K8 K11) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r) | clear - K6l K6r K8 K11; lia | clear - K6l K6r K8 K11; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r) | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K15l K15r) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaqSAs4.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaqSAs4.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 96) <= bv_unsigned a < (vz_2 - 96) + 96) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PaqSAs4.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K11 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaqSAs4.ps0) with 0xaf02c in Hms. change (SR.ps_regs PaqSAs4.ps0) with (map (fun i => (i, nth i PaqSAs4.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaqSAs4.ps0) with PaqSAs4.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaqSAs4.regs0 PaqSAs4.regs_out0 60 KS_aqSAs4 KS_aqSAs4_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaqSAs4.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaqSAs4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSAs4.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaqSAs4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSAs4.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaqSAs4.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PaqSAs4.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PaqSAs4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSAs4.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaqSAs4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSAs4.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaqSAs4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSAs4.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PaqSAs4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSAs4.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PaqSAs4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSAs4.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaqSAs4.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PaqSAs4.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaqSAs4.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PaqSAs4.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PaqSAs4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSAs4.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PaqSAs4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PaqSB := BndP_Ea_038S8.LibSegEa_aqSB.
Definition KS_aqSB : list nat := Eval vm_compute in (BG.kept_list 60 PaqSB.regs0 PaqSB.regs_out0).
Lemma KS_aqSB_ok : BG.kept_ok 60 PaqSB.regs0 PaqSB.regs_out0 KS_aqSB = true. Proof. vm_compute. reflexivity. Qed.
Lemma aqSB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 14%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 13) = Z_to_bv 64 (V 58%nat) -> getr R (reg 14) = Z_to_bv 64 (V 59%nat) -> getr R (reg 18) = Z_to_bv 64 (V 11%nat) -> getr R (reg 19) = Z_to_bv 64 (V 14%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 38%nat) ->
  L5.img_clear M 1253376 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487264 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 -> 4096 <= (V 10%nat) <= 140737488355272 -> aligned (V 10%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 -> L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> (((V 2%nat) - 96) + 96 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 96)) ->
  L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 4096 <= (V 11%nat) <= 140737488355312 ->
  aligned (V 11%nat) 8 -> (2147446784 + 17592186048512 <= (V 11%nat) \/ (V 11%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 11%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 11%nat) + 8) / 8) + 2147450880) 1 ->
  ((V 11%nat) + 16 <= ((V 2%nat) - 96) \/ ((V 2%nat) - 96) + 96 <= (V 11%nat)) -> L5.u64_at RSEGS M (V 11%nat) (V 33%nat) -> L5.u64_at RSEGS M ((V 11%nat) + 8) (V 34%nat) -> 0 <= (V 33%nat) <= 140737488355328 ->
  0 <= (V 34%nat) <= 67108864 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac460 M) (st fx' R' 0xb1068 M')
        /\ (forall x, In x KS_aqSB -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 705680
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 11%nat) + 8)
        /\ getr R' (reg 23) = Z_to_bv 64 (((V 11%nat) / 8) + 2147450880)
        /\ getr R' (reg 24) = Z_to_bv 64 ((((V 11%nat) + 8) / 8) + 2147450880)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 G2 G8 G9 G10 G11 G12 G13 G14 G18 G19 G21 G22 K0 K1 K2 pvzI14 K4 K5 pvzI15 K7 K8 K9 K10 K11 K12 pvzI16 K14 pvzI17 K16 K17 K18 K19 K20 K21 K22 pvzI18 pvzI19.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV11l; move HV11l before pvzI3; pose proof (proj2 pvzI3) as HV11r; move HV11r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV14l; move HV14l before pvzI4; pose proof (proj2 pvzI4) as HV14r; move HV14r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV33l; move HV33l before pvzI5; pose proof (proj2 pvzI5) as HV33r; move HV33r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV34l; move HV34l before pvzI6; pose proof (proj2 pvzI6) as HV34r; move HV34r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV38l; move HV38l before pvzI7; pose proof (proj2 pvzI7) as HV38r; move HV38r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV41l; move HV41l before pvzI8; pose proof (proj2 pvzI8) as HV41r; move HV41r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV55l; move HV55l before pvzI9; pose proof (proj2 pvzI9) as HV55r; move HV55r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV56l; move HV56l before pvzI10; pose proof (proj2 pvzI10) as HV56r; move HV56r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV57l; move HV57l before pvzI11; pose proof (proj2 pvzI11) as HV57r; move HV57r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV58l; move HV58l before pvzI12; pose proof (proj2 pvzI12) as HV58r; move HV58r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV59l; move HV59l before pvzI13; pose proof (proj2 pvzI13) as HV59r; move HV59r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K3l; move K3l before pvzI14; pose proof (proj2 pvzI14) as K3r; move K3r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K6l; move K6l before pvzI15; pose proof (proj2 pvzI15) as K6r; move K6r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K13l; move K13l before pvzI16; pose proof (proj2 pvzI16) as K13r; move K13r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K15l; move K15l before pvzI17; pose proof (proj2 pvzI17) as K15r; move K15r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K23l; move K23l before pvzI18; pose proof (proj2 pvzI18) as K23r; move K23r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K24l; move K24l before pvzI19; pose proof (proj2 pvzI19) as K24r; move K24r before pvzI19; clear pvzI19.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_14 := V 14%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *. set (vz_59 := V 59%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 11%nat => Z_to_bv 64 vz_11 | 14%nat => Z_to_bv 64 vz_14 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 38%nat => Z_to_bv 64 vz_38 | 41%nat => Z_to_bv 64 vz_41 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | 59%nat => Z_to_bv 64 vz_59 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 11%nat => vz_11 | 14%nat => vz_14 | 33%nat => vz_33 | 34%nat => vz_34 | 38%nat => vz_38 | 41%nat => vz_41 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 58%nat => vz_58 | 59%nat => vz_59 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 60%nat. }
  assert (HR: regs_ok E PaqSB.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaqSB.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaqSB.kn0).
  { unfold know_ok, PaqSB.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K20) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K20) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K20) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K20; lia | clear - HV2l HV2r K3l K3r K11 K20; lia | clear - HV2l HV2r K3l K3r K11 K20; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K6l K6r K8 K11; lia | clear - HV10l HV10r K6l K6r K8 K11; lia | clear - HV10l HV10r K6l K6r K8 K11; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K6l K6r K8 K11; lia | clear - HV10l HV10r K6l K6r K8 K11; lia | clear - HV10l HV10r K6l K6r K8 K11; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r) | clear - HV10l HV10r K6l K6r K8 K11; lia | clear - HV10l HV10r K6l K6r K8 K11; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r) | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV11l HV11r K15l K15r K17 K20) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV11l HV11r K15l K15r K17 K20) | clear; lia | exact K16]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV11l HV11r K15l K15r K17 K20) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV11l HV11r K15l K15r K17 K20) | evalEk ZA ltac:(clear) | clear - HV11l HV11r K15l K15r K17 K20; lia | clear - HV11l HV11r K15l K15r K17 K20; lia | clear - HV11l HV11r K15l K15r K17 K20; lia | exactA K18]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV11l HV11r K15l K15r K17 K20) | evalEk ZA ltac:(clear) | clear - HV11l HV11r K15l K15r K17 K20; lia | clear - HV11l HV11r K15l K15r K17 K20; lia | clear - HV11l HV11r K15l K15r K17 K20; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV11l HV11r K15l K15r K17 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K20) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV11l HV11r K15l K15r K17 K20) | evalEk ZA ltac:(clear - HV33l HV33r K23l K23r) | clear - HV11l HV11r K15l K15r K17 K20; lia | clear - HV11l HV11r K15l K15r K17 K20; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV11l HV11r K15l K15r K17 K20) | evalEk ZA ltac:(clear - HV34l HV34r K24l K24r) | clear - HV11l HV11r K15l K15r K17 K20; lia | clear - HV11l HV11r K15l K15r K17 K20; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K24l K24r) | exact (conj K24l K24r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaqSB.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaqSB.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PaqSB.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaqSB.ps0) with 0xb1068 in Hms. change (SR.ps_regs PaqSB.ps0) with (map (fun i => (i, nth i PaqSB.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaqSB.ps0) with PaqSB.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaqSB.regs0 PaqSB.regs_out0 60 KS_aqSB KS_aqSB_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaqSB.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaqSB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSB.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaqSB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSB.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaqSB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSB.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PaqSB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSB.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PaqSB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PaqSB.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PaqSB.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PaqSCe := BndP_Ea_038S8.LibSegEa_aqSCe.
Definition KS_aqSCe : list nat := Eval vm_compute in (BG.kept_list 60 PaqSCe.regs0 PaqSCe.regs_out0).
Lemma KS_aqSCe_ok : BG.kept_ok 60 PaqSCe.regs0 PaqSCe.regs_out0 KS_aqSCe = true. Proof. vm_compute. reflexivity. Qed.
Lemma aqSCe_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 14%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 35%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 13) = Z_to_bv 64 (V 58%nat) -> getr R (reg 14) = Z_to_bv 64 (V 59%nat) -> getr R (reg 18) = Z_to_bv 64 (V 11%nat) -> getr R (reg 19) = Z_to_bv 64 (V 14%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 11%nat) + 8) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 38%nat) -> getr R (reg 23) = Z_to_bv 64 (V 39%nat) -> getr R (reg 24) = Z_to_bv 64 (V 54%nat) ->
  L5.img_clear M 1253376 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487264 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 -> 1 <= (V 35%nat) <= 6 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac490 M) (st fx' R' 0xae310 M')
        /\ (forall x, In x KS_aqSCe -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 705700
        /\ getr R' (reg 10) = Z_to_bv 64 (V 14%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 7).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 G2 G8 G9 G10 G11 G12 G13 G14 G18 G19 G20 G21 G22 G23 G24 K0 K1 K2 pvzI13 K4 K5 pvzI14.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV11l; move HV11l before pvzI3; pose proof (proj2 pvzI3) as HV11r; move HV11r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV14l; move HV14l before pvzI4; pose proof (proj2 pvzI4) as HV14r; move HV14r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV35l; move HV35l before pvzI5; pose proof (proj2 pvzI5) as HV35r; move HV35r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV39l; move HV39l before pvzI7; pose proof (proj2 pvzI7) as HV39r; move HV39r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV54l; move HV54l before pvzI8; pose proof (proj2 pvzI8) as HV54r; move HV54r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV55l; move HV55l before pvzI9; pose proof (proj2 pvzI9) as HV55r; move HV55r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV57l; move HV57l before pvzI10; pose proof (proj2 pvzI10) as HV57r; move HV57r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV58l; move HV58l before pvzI11; pose proof (proj2 pvzI11) as HV58r; move HV58r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV59l; move HV59l before pvzI12; pose proof (proj2 pvzI12) as HV59r; move HV59r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K3l; move K3l before pvzI13; pose proof (proj2 pvzI13) as K3r; move K3r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K6l; move K6l before pvzI14; pose proof (proj2 pvzI14) as K6r; move K6r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_14 := V 14%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_54 := V 54%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *. set (vz_59 := V 59%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 11%nat => Z_to_bv 64 vz_11 | 14%nat => Z_to_bv 64 vz_14 | 35%nat => Z_to_bv 64 vz_35 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 54%nat => Z_to_bv 64 vz_54 | 55%nat => Z_to_bv 64 vz_55 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | 59%nat => Z_to_bv 64 vz_59 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 11%nat => vz_11 | 14%nat => vz_14 | 35%nat => vz_35 | 38%nat => vz_38 | 39%nat => vz_39 | 54%nat => vz_54 | 55%nat => vz_55 | 57%nat => vz_57 | 58%nat => vz_58 | 59%nat => vz_59 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 60%nat. }
  assert (HR: regs_ok E PaqSCe.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaqSCe.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaqSCe.kn0).
  { unfold know_ok, PaqSCe.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaqSCe.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaqSCe.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PaqSCe.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaqSCe.ps0) with 0xae310 in Hms. change (SR.ps_regs PaqSCe.ps0) with (map (fun i => (i, nth i PaqSCe.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaqSCe.ps0) with PaqSCe.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaqSCe.regs0 PaqSCe.regs_out0 60 KS_aqSCe KS_aqSCe_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaqSCe.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaqSCe.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSCe.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaqSCe.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PaqSCe.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaqSCe.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PaqSCo := BndP_Ea_038S8.LibSegEa_aqSCo.
Definition KS_aqSCo : list nat := Eval vm_compute in (BG.kept_list 60 PaqSCo.regs0 PaqSCo.regs_out0).
Lemma KS_aqSCo_ok : BG.kept_ok 60 PaqSCo.regs0 PaqSCo.regs_out0 KS_aqSCo = true. Proof. vm_compute. reflexivity. Qed.
Lemma aqSCo_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 14%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 0 -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 13) = Z_to_bv 64 (V 58%nat) -> getr R (reg 14) = Z_to_bv 64 (V 59%nat) -> getr R (reg 18) = Z_to_bv 64 (V 11%nat) -> getr R (reg 19) = Z_to_bv 64 (V 14%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 11%nat) + 8) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 38%nat) -> getr R (reg 23) = Z_to_bv 64 (V 39%nat) -> getr R (reg 24) = Z_to_bv 64 (V 54%nat) ->
  L5.img_clear M 1253376 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487264 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 -> 4096 <= (V 10%nat) <= 140737488355272 -> aligned (V 10%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 -> L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> (((V 2%nat) - 96) + 96 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 96)) ->
  L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 4096 <= (V 11%nat) <= 140737488355312 ->
  aligned (V 11%nat) 8 -> (2147446784 + 17592186048512 <= (V 11%nat) \/ (V 11%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 11%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 11%nat) + 8) / 8) + 2147450880) 1 ->
  ((V 11%nat) + 16 <= ((V 2%nat) - 96) \/ ((V 2%nat) - 96) + 96 <= (V 11%nat)) -> L5.u64_at RSEGS M (V 11%nat) (V 33%nat) -> L5.u64_at RSEGS M ((V 11%nat) + 8) (V 34%nat) -> 0 <= (V 33%nat) <= 140737488355328 ->
  0 <= (V 34%nat) <= 67108864 -> L5KA.zeros_at M (V 39%nat) 2 -> 2147451392 <= (V 39%nat) <= 19791209299968 -> L5KA.zeros_at M (V 54%nat) 1 ->
  2147451393 <= (V 54%nat) <= 19791209299968 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac490 M) (st fx' R' 0xae710 M')
        /\ (forall x, In x KS_aqSCo -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 705724
        /\ getr R' (reg 10) = Z_to_bv 64 (V 10%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 34%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 G2 G8 G9 G10 G11 G12 G13 G14 G18 G19 G20 G21 G22 G23 G24 K0 K1 K2 pvzI15 K4 K5 pvzI16 K7 K8 K9 K10 K11 K12 pvzI17 K14 pvzI18 K16 K17 K18 K19 K20 K21 K22 pvzI19 pvzI20 K25 pvzI21 K27 pvzI22.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV11l; move HV11l before pvzI3; pose proof (proj2 pvzI3) as HV11r; move HV11r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV14l; move HV14l before pvzI4; pose proof (proj2 pvzI4) as HV14r; move HV14r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV33l; move HV33l before pvzI5; pose proof (proj2 pvzI5) as HV33r; move HV33r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV34l; move HV34l before pvzI6; pose proof (proj2 pvzI6) as HV34r; move HV34r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV38l; move HV38l before pvzI7; pose proof (proj2 pvzI7) as HV38r; move HV38r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV39l; move HV39l before pvzI8; pose proof (proj2 pvzI8) as HV39r; move HV39r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV41l; move HV41l before pvzI9; pose proof (proj2 pvzI9) as HV41r; move HV41r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV54l; move HV54l before pvzI10; pose proof (proj2 pvzI10) as HV54r; move HV54r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV55l; move HV55l before pvzI11; pose proof (proj2 pvzI11) as HV55r; move HV55r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV57l; move HV57l before pvzI12; pose proof (proj2 pvzI12) as HV57r; move HV57r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV58l; move HV58l before pvzI13; pose proof (proj2 pvzI13) as HV58r; move HV58r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV59l; move HV59l before pvzI14; pose proof (proj2 pvzI14) as HV59r; move HV59r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K3l; move K3l before pvzI15; pose proof (proj2 pvzI15) as K3r; move K3r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K6l; move K6l before pvzI16; pose proof (proj2 pvzI16) as K6r; move K6r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K13l; move K13l before pvzI17; pose proof (proj2 pvzI17) as K13r; move K13r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K15l; move K15l before pvzI18; pose proof (proj2 pvzI18) as K15r; move K15r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K23l; move K23l before pvzI19; pose proof (proj2 pvzI19) as K23r; move K23r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K24l; move K24l before pvzI20; pose proof (proj2 pvzI20) as K24r; move K24r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K26l; move K26l before pvzI21; pose proof (proj2 pvzI21) as K26r; move K26r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K28l; move K28l before pvzI22; pose proof (proj2 pvzI22) as K28r; move K28r before pvzI22; clear pvzI22.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_14 := V 14%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_54 := V 54%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *. set (vz_59 := V 59%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 11%nat => Z_to_bv 64 vz_11 | 14%nat => Z_to_bv 64 vz_14 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 41%nat => Z_to_bv 64 vz_41 | 54%nat => Z_to_bv 64 vz_54 | 55%nat => Z_to_bv 64 vz_55 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | 59%nat => Z_to_bv 64 vz_59 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 11%nat => vz_11 | 14%nat => vz_14 | 33%nat => vz_33 | 34%nat => vz_34 | 38%nat => vz_38 | 39%nat => vz_39 | 41%nat => vz_41 | 54%nat => vz_54 | 55%nat => vz_55 | 57%nat => vz_57 | 58%nat => vz_58 | 59%nat => vz_59 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 60%nat. }
  assert (HR: regs_ok E PaqSCo.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaqSCo.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaqSCo.kn0).
  { unfold know_ok, PaqSCo.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K20) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K20) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K20) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K20; lia | clear - HV2l HV2r K3l K3r K11 K20; lia | clear - HV2l HV2r K3l K3r K11 K20; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K6l K6r K8 K11; lia | clear - HV10l HV10r K6l K6r K8 K11; lia | clear - HV10l HV10r K6l K6r K8 K11; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K6l K6r K8 K11; lia | clear - HV10l HV10r K6l K6r K8 K11; lia | clear - HV10l HV10r K6l K6r K8 K11; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r) | clear - HV10l HV10r K6l K6r K8 K11; lia | clear - HV10l HV10r K6l K6r K8 K11; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r) | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV11l HV11r K15l K15r K17 K20) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV11l HV11r K15l K15r K17 K20) | clear; lia | exact K16]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV11l HV11r K15l K15r K17 K20) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV11l HV11r K15l K15r K17 K20) | evalEk ZA ltac:(clear) | clear - HV11l HV11r K15l K15r K17 K20; lia | clear - HV11l HV11r K15l K15r K17 K20; lia | clear - HV11l HV11r K15l K15r K17 K20; lia | exactA K18]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV11l HV11r K15l K15r K17 K20) | evalEk ZA ltac:(clear) | clear - HV11l HV11r K15l K15r K17 K20; lia | clear - HV11l HV11r K15l K15r K17 K20; lia | clear - HV11l HV11r K15l K15r K17 K20; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV11l HV11r K15l K15r K17 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K20) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV11l HV11r K15l K15r K17 K20) | evalEk ZA ltac:(clear - HV33l HV33r K23l K23r) | clear - HV11l HV11r K15l K15r K17 K20; lia | clear - HV11l HV11r K15l K15r K17 K20; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV11l HV11r K15l K15r K17 K20) | evalEk ZA ltac:(clear - HV34l HV34r K24l K24r) | clear - HV11l HV11r K15l K15r K17 K20; lia | clear - HV11l HV11r K15l K15r K17 K20; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K24l K24r) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV39l HV39r K26l K26r) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K26l K26r; lia | clear - HV39l HV39r K26l K26r; lia | clear - HV39l HV39r K26l K26r; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K26l K26r) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV54l HV54r K28l K28r) | evalEk ZA ltac:(clear) | clear - HV54l HV54r K28l K28r; lia | clear - HV54l HV54r K28l K28r; lia | clear - HV54l HV54r K28l K28r; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV54l HV54r K28l K28r) | exact (conj K28l K28r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaqSCo.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaqSCo.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PaqSCo.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaqSCo.ps0) with 0xae710 in Hms. change (SR.ps_regs PaqSCo.ps0) with (map (fun i => (i, nth i PaqSCo.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaqSCo.ps0) with PaqSCo.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaqSCo.regs0 PaqSCo.regs_out0 60 KS_aqSCo KS_aqSCo_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaqSCo.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaqSCo.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSCo.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaqSCo.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PaqSCo.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaqSCo.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PaqSD0 := BndP_Ea_038S8.LibSegEa_aqSD0.
Definition KS_aqSD0 : list nat := Eval vm_compute in (BG.kept_list 60 PaqSD0.regs0 PaqSD0.regs_out0).
Lemma KS_aqSD0_ok : BG.kept_ok 60 PaqSD0.regs0 PaqSD0.regs_out0 KS_aqSD0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma aqSD0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 14%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 13) = Z_to_bv 64 (V 58%nat) -> getr R (reg 14) = Z_to_bv 64 (V 59%nat) -> getr R (reg 18) = Z_to_bv 64 (V 11%nat) -> getr R (reg 19) = Z_to_bv 64 (V 14%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 11%nat) + 8) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 38%nat) -> getr R (reg 23) = Z_to_bv 64 (V 39%nat) -> getr R (reg 24) = Z_to_bv 64 (V 54%nat) ->
  L5.img_clear M 1253376 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487264 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 -> 4096 <= (V 10%nat) <= 140737488355272 -> aligned (V 10%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 -> L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> (((V 2%nat) - 96) + 96 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 96)) ->
  L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 4096 <= (V 11%nat) <= 140737488355312 ->
  aligned (V 11%nat) 8 -> (2147446784 + 17592186048512 <= (V 11%nat) \/ (V 11%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 11%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 11%nat) + 8) / 8) + 2147450880) 1 ->
  ((V 11%nat) + 16 <= ((V 2%nat) - 96) \/ ((V 2%nat) - 96) + 96 <= (V 11%nat)) -> L5.u64_at RSEGS M (V 11%nat) (V 33%nat) -> L5.u64_at RSEGS M ((V 11%nat) + 8) 0 -> 0 <= (V 33%nat) <= 140737488355328 ->
  L5KA.zeros_at M (V 39%nat) 2 -> 2147451392 <= (V 39%nat) <= 19791209299968 -> L5KA.zeros_at M (V 54%nat) 1 -> 2147451393 <= (V 54%nat) <= 19791209299968 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac4bc M) (st fx' R' 0xac52c M')
        /\ (forall x, In x KS_aqSD0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 19) = Z_to_bv 64 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 G2 G8 G9 G10 G11 G12 G13 G14 G18 G19 G20 G21 G22 G23 G24 K0 K1 K2 pvzI15 K4 K5 pvzI16 K7 K8 K9 K10 K11 K12 pvzI17 K14 pvzI18 K16 K17 K18 K19 K20 K21 K22 pvzI19 K24 pvzI20 K26 pvzI21.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV11l; move HV11l before pvzI3; pose proof (proj2 pvzI3) as HV11r; move HV11r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV14l; move HV14l before pvzI4; pose proof (proj2 pvzI4) as HV14r; move HV14r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV33l; move HV33l before pvzI5; pose proof (proj2 pvzI5) as HV33r; move HV33r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV39l; move HV39l before pvzI7; pose proof (proj2 pvzI7) as HV39r; move HV39r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV41l; move HV41l before pvzI8; pose proof (proj2 pvzI8) as HV41r; move HV41r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV54l; move HV54l before pvzI9; pose proof (proj2 pvzI9) as HV54r; move HV54r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV55l; move HV55l before pvzI10; pose proof (proj2 pvzI10) as HV55r; move HV55r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV56l; move HV56l before pvzI11; pose proof (proj2 pvzI11) as HV56r; move HV56r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV57l; move HV57l before pvzI12; pose proof (proj2 pvzI12) as HV57r; move HV57r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV58l; move HV58l before pvzI13; pose proof (proj2 pvzI13) as HV58r; move HV58r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV59l; move HV59l before pvzI14; pose proof (proj2 pvzI14) as HV59r; move HV59r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K3l; move K3l before pvzI15; pose proof (proj2 pvzI15) as K3r; move K3r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K6l; move K6l before pvzI16; pose proof (proj2 pvzI16) as K6r; move K6r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K13l; move K13l before pvzI17; pose proof (proj2 pvzI17) as K13r; move K13r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K15l; move K15l before pvzI18; pose proof (proj2 pvzI18) as K15r; move K15r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K23l; move K23l before pvzI19; pose proof (proj2 pvzI19) as K23r; move K23r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K25l; move K25l before pvzI20; pose proof (proj2 pvzI20) as K25r; move K25r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K27l; move K27l before pvzI21; pose proof (proj2 pvzI21) as K27r; move K27r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_14 := V 14%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_54 := V 54%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *. set (vz_59 := V 59%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 11%nat => Z_to_bv 64 vz_11 | 14%nat => Z_to_bv 64 vz_14 | 33%nat => Z_to_bv 64 vz_33 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 41%nat => Z_to_bv 64 vz_41 | 54%nat => Z_to_bv 64 vz_54 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | 59%nat => Z_to_bv 64 vz_59 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 11%nat => vz_11 | 14%nat => vz_14 | 33%nat => vz_33 | 38%nat => vz_38 | 39%nat => vz_39 | 41%nat => vz_41 | 54%nat => vz_54 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 58%nat => vz_58 | 59%nat => vz_59 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 60%nat. }
  assert (HR: regs_ok E PaqSD0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaqSD0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaqSD0.kn0).
  { unfold know_ok, PaqSD0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K20) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K20) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K20) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K20; lia | clear - HV2l HV2r K3l K3r K11 K20; lia | clear - HV2l HV2r K3l K3r K11 K20; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K6l K6r K8 K11; lia | clear - HV10l HV10r K6l K6r K8 K11; lia | clear - HV10l HV10r K6l K6r K8 K11; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K6l K6r K8 K11; lia | clear - HV10l HV10r K6l K6r K8 K11; lia | clear - HV10l HV10r K6l K6r K8 K11; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r) | clear - HV10l HV10r K6l K6r K8 K11; lia | clear - HV10l HV10r K6l K6r K8 K11; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r) | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV11l HV11r K15l K15r K17 K20) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV11l HV11r K15l K15r K17 K20) | clear; lia | exact K16]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV11l HV11r K15l K15r K17 K20) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV11l HV11r K15l K15r K17 K20) | evalEk ZA ltac:(clear) | clear - HV11l HV11r K15l K15r K17 K20; lia | clear - HV11l HV11r K15l K15r K17 K20; lia | clear - HV11l HV11r K15l K15r K17 K20; lia | exactA K18]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV11l HV11r K15l K15r K17 K20) | evalEk ZA ltac:(clear) | clear - HV11l HV11r K15l K15r K17 K20; lia | clear - HV11l HV11r K15l K15r K17 K20; lia | clear - HV11l HV11r K15l K15r K17 K20; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV11l HV11r K15l K15r K17 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K20) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV11l HV11r K15l K15r K17 K20) | evalEk ZA ltac:(clear - HV33l HV33r K23l K23r) | clear - HV11l HV11r K15l K15r K17 K20; lia | clear - HV11l HV11r K15l K15r K17 K20; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV11l HV11r K15l K15r K17 K20) | evalEk ZA ltac:(clear) | clear - HV11l HV11r K15l K15r K17 K20; lia | clear - HV11l HV11r K15l K15r K17 K20; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV39l HV39r K25l K25r) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K25l K25r; lia | clear - HV39l HV39r K25l K25r; lia | clear - HV39l HV39r K25l K25r; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV54l HV54r K27l K27r) | evalEk ZA ltac:(clear) | clear - HV54l HV54r K27l K27r; lia | clear - HV54l HV54r K27l K27r; lia | clear - HV54l HV54r K27l K27r; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV54l HV54r K27l K27r) | exact (conj K27l K27r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaqSD0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaqSD0.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PaqSD0.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaqSD0.ps0) with 0xac52c in Hms. change (SR.ps_regs PaqSD0.ps0) with (map (fun i => (i, nth i PaqSD0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaqSD0.ps0) with PaqSD0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaqSD0.regs0 PaqSD0.regs_out0 60 KS_aqSD0 KS_aqSD0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaqSD0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaqSD0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PaqSD0.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaqSD0.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PaqSD1 := BndP_Ea_038S8.LibSegEa_aqSD1.
Definition KS_aqSD1 : list nat := Eval vm_compute in (BG.kept_list 60 PaqSD1.regs0 PaqSD1.regs_out0).
Lemma KS_aqSD1_ok : BG.kept_ok 60 PaqSD1.regs0 PaqSD1.regs_out0 KS_aqSD1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma aqSD1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 14%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 13) = Z_to_bv 64 (V 58%nat) -> getr R (reg 14) = Z_to_bv 64 (V 59%nat) -> getr R (reg 18) = Z_to_bv 64 (V 11%nat) -> getr R (reg 19) = Z_to_bv 64 (V 14%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 11%nat) + 8) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 38%nat) -> getr R (reg 23) = Z_to_bv 64 (V 39%nat) -> getr R (reg 24) = Z_to_bv 64 (V 54%nat) ->
  L5.img_clear M 1253376 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487264 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 -> 4096 <= (V 10%nat) <= 140737488355272 -> aligned (V 10%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 -> L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> (((V 2%nat) - 96) + 96 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 96)) ->
  L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 4096 <= (V 11%nat) <= 140737488355312 ->
  aligned (V 11%nat) 8 -> (2147446784 + 17592186048512 <= (V 11%nat) \/ (V 11%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 11%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 11%nat) + 8) / 8) + 2147450880) 1 ->
  ((V 11%nat) + 16 <= ((V 2%nat) - 96) \/ ((V 2%nat) - 96) + 96 <= (V 11%nat)) -> L5.u64_at RSEGS M (V 11%nat) (V 33%nat) -> L5.u64_at RSEGS M ((V 11%nat) + 8) (V 34%nat) -> 1 <= (V 33%nat) <= 140737488355326 ->
  1 <= (V 34%nat) <= 67108864 -> L5KA.zeros_at M (V 39%nat) 2 -> 2147451392 <= (V 39%nat) <= 19791209299968 -> L5KA.zeros_at M (V 54%nat) 1 ->
  2147451393 <= (V 54%nat) <= 19791209299968 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac4bc M) (st fx' R' 0xac4dc M')
        /\ (forall x, In x KS_aqSD1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 33%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 G2 G8 G9 G10 G11 G12 G13 G14 G18 G19 G20 G21 G22 G23 G24 K0 K1 K2 pvzI16 K4 K5 pvzI17 K7 K8 K9 K10 K11 K12 pvzI18 K14 pvzI19 K16 K17 K18 K19 K20 K21 K22 pvzI20 pvzI21 K25 pvzI22 K27 pvzI23.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV11l; move HV11l before pvzI3; pose proof (proj2 pvzI3) as HV11r; move HV11r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV14l; move HV14l before pvzI4; pose proof (proj2 pvzI4) as HV14r; move HV14r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV33l; move HV33l before pvzI5; pose proof (proj2 pvzI5) as HV33r; move HV33r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV34l; move HV34l before pvzI6; pose proof (proj2 pvzI6) as HV34r; move HV34r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV38l; move HV38l before pvzI7; pose proof (proj2 pvzI7) as HV38r; move HV38r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV39l; move HV39l before pvzI8; pose proof (proj2 pvzI8) as HV39r; move HV39r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV41l; move HV41l before pvzI9; pose proof (proj2 pvzI9) as HV41r; move HV41r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV54l; move HV54l before pvzI10; pose proof (proj2 pvzI10) as HV54r; move HV54r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV55l; move HV55l before pvzI11; pose proof (proj2 pvzI11) as HV55r; move HV55r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV56l; move HV56l before pvzI12; pose proof (proj2 pvzI12) as HV56r; move HV56r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV57l; move HV57l before pvzI13; pose proof (proj2 pvzI13) as HV57r; move HV57r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV58l; move HV58l before pvzI14; pose proof (proj2 pvzI14) as HV58r; move HV58r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV59l; move HV59l before pvzI15; pose proof (proj2 pvzI15) as HV59r; move HV59r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K3l; move K3l before pvzI16; pose proof (proj2 pvzI16) as K3r; move K3r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K6l; move K6l before pvzI17; pose proof (proj2 pvzI17) as K6r; move K6r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K13l; move K13l before pvzI18; pose proof (proj2 pvzI18) as K13r; move K13r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K15l; move K15l before pvzI19; pose proof (proj2 pvzI19) as K15r; move K15r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K23l; move K23l before pvzI20; pose proof (proj2 pvzI20) as K23r; move K23r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K24l; move K24l before pvzI21; pose proof (proj2 pvzI21) as K24r; move K24r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K26l; move K26l before pvzI22; pose proof (proj2 pvzI22) as K26r; move K26r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K28l; move K28l before pvzI23; pose proof (proj2 pvzI23) as K28r; move K28r before pvzI23; clear pvzI23.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_11 := V 11%nat) in *. set (vz_14 := V 14%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_54 := V 54%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *. set (vz_59 := V 59%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 11%nat => Z_to_bv 64 vz_11 | 14%nat => Z_to_bv 64 vz_14 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 41%nat => Z_to_bv 64 vz_41 | 54%nat => Z_to_bv 64 vz_54 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | 59%nat => Z_to_bv 64 vz_59 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 11%nat => vz_11 | 14%nat => vz_14 | 33%nat => vz_33 | 34%nat => vz_34 | 38%nat => vz_38 | 39%nat => vz_39 | 41%nat => vz_41 | 54%nat => vz_54 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 58%nat => vz_58 | 59%nat => vz_59 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 60%nat. }
  assert (HR: regs_ok E PaqSD1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaqSD1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaqSD1.kn0).
  { unfold know_ok, PaqSD1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K20) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K20) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K20) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K20; lia | clear - HV2l HV2r K3l K3r K11 K20; lia | clear - HV2l HV2r K3l K3r K11 K20; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K6l K6r K8 K11; lia | clear - HV10l HV10r K6l K6r K8 K11; lia | clear - HV10l HV10r K6l K6r K8 K11; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K6l K6r K8 K11; lia | clear - HV10l HV10r K6l K6r K8 K11; lia | clear - HV10l HV10r K6l K6r K8 K11; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r) | clear - HV10l HV10r K6l K6r K8 K11; lia | clear - HV10l HV10r K6l K6r K8 K11; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r) | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV11l HV11r K15l K15r K17 K20) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV11l HV11r K15l K15r K17 K20) | clear; lia | exact K16]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV11l HV11r K15l K15r K17 K20) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV11l HV11r K15l K15r K17 K20) | evalEk ZA ltac:(clear) | clear - HV11l HV11r K15l K15r K17 K20; lia | clear - HV11l HV11r K15l K15r K17 K20; lia | clear - HV11l HV11r K15l K15r K17 K20; lia | exactA K18]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV11l HV11r K15l K15r K17 K20) | evalEk ZA ltac:(clear) | clear - HV11l HV11r K15l K15r K17 K20; lia | clear - HV11l HV11r K15l K15r K17 K20; lia | clear - HV11l HV11r K15l K15r K17 K20; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV11l HV11r K15l K15r K17 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K20) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV11l HV11r K15l K15r K17 K20) | evalEk ZA ltac:(clear - HV33l HV33r K23l K23r) | clear - HV11l HV11r K15l K15r K17 K20; lia | clear - HV11l HV11r K15l K15r K17 K20; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV11l HV11r K15l K15r K17 K20) | evalEk ZA ltac:(clear - HV34l HV34r K24l K24r) | clear - HV11l HV11r K15l K15r K17 K20; lia | clear - HV11l HV11r K15l K15r K17 K20; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K24l K24r) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV39l HV39r K26l K26r) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K26l K26r; lia | clear - HV39l HV39r K26l K26r; lia | clear - HV39l HV39r K26l K26r; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K26l K26r) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV54l HV54r K28l K28r) | evalEk ZA ltac:(clear) | clear - HV54l HV54r K28l K28r; lia | clear - HV54l HV54r K28l K28r; lia | clear - HV54l HV54r K28l K28r; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV54l HV54r K28l K28r) | exact (conj K28l K28r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaqSD1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaqSD1.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PaqSD1.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaqSD1.ps0) with 0xac4dc in Hms. change (SR.ps_regs PaqSD1.ps0) with (map (fun i => (i, nth i PaqSD1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaqSD1.ps0) with PaqSD1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaqSD1.regs0 PaqSD1.regs_out0 60 KS_aqSD1 KS_aqSD1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaqSD1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaqSD1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSD1.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaqSD1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSD1.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaqSD1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PaqSD1.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PaqSD1.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PaqSE := BndP_Ea_038S8.LibSegEa_aqSE.
Definition KS_aqSE : list nat := Eval vm_compute in (BG.kept_list 60 PaqSE.regs0 PaqSE.regs_out0).
Lemma KS_aqSE_ok : BG.kept_ok 60 PaqSE.regs0 PaqSE.regs_out0 KS_aqSE = true. Proof. vm_compute. reflexivity. Qed.
Lemma aqSE_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 13) = Z_to_bv 64 (V 58%nat) -> getr R (reg 14) = Z_to_bv 64 (V 59%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 (V 37%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 38%nat) ->
  L5.img_clear M 1253376 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487264 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 -> 4096 <= (V 10%nat) <= 140737488355272 -> aligned (V 10%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 -> L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> (((V 2%nat) - 96) + 96 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 96)) ->
  L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> L5KA.zeros_at M (V 38%nat) 1 ->
  2147451393 <= (V 38%nat) <= 19791209299968 -> 1 <= (V 36%nat) <= 140737488355326 -> 1 <= (V 37%nat) <= 67108864 -> L5.u8_at RSEGS M (V 36%nat) (V 40%nat) ->
  0 <= (V 40%nat) <= 255 -> ((V 36%nat) + 1 <= ((V 2%nat) - 96) \/ ((V 2%nat) - 96) + 96 <= (V 36%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 81) <= bv_unsigned a < ((V 2%nat) - 81) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 81) <= i < ((V 2%nat) - 81) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac4ec M) (st fx' R' 0xaf02c M')
        /\ (forall x, In x KS_aqSE -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 705800
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 81)
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 81) (V 40%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 G2 G8 G9 G10 G11 G12 G13 G14 G18 G19 G20 G21 G22 K0 K1 K2 pvzI13 K4 K5 pvzI14 K7 K8 K9 K10 K11 K12 pvzI15 K14 K15 pvzI16 pvzI17 pvzI18 K19 pvzI19 K21.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV40l; move HV40l before pvzI6; pose proof (proj2 pvzI6) as HV40r; move HV40r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV41l; move HV41l before pvzI7; pose proof (proj2 pvzI7) as HV41r; move HV41r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV55l; move HV55l before pvzI8; pose proof (proj2 pvzI8) as HV55r; move HV55r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV56l; move HV56l before pvzI9; pose proof (proj2 pvzI9) as HV56r; move HV56r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV57l; move HV57l before pvzI10; pose proof (proj2 pvzI10) as HV57r; move HV57r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV58l; move HV58l before pvzI11; pose proof (proj2 pvzI11) as HV58r; move HV58r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV59l; move HV59l before pvzI12; pose proof (proj2 pvzI12) as HV59r; move HV59r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K3l; move K3l before pvzI13; pose proof (proj2 pvzI13) as K3r; move K3r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K6l; move K6l before pvzI14; pose proof (proj2 pvzI14) as K6r; move K6r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K13l; move K13l before pvzI15; pose proof (proj2 pvzI15) as K13r; move K13r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K16l; move K16l before pvzI16; pose proof (proj2 pvzI16) as K16r; move K16r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K17l; move K17l before pvzI17; pose proof (proj2 pvzI17) as K17r; move K17r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K18l; move K18l before pvzI18; pose proof (proj2 pvzI18) as K18r; move K18r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K20l; move K20l before pvzI19; pose proof (proj2 pvzI19) as K20r; move K20r before pvzI19; clear pvzI19.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *. set (vz_59 := V 59%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | 59%nat => Z_to_bv 64 vz_59 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 40%nat => vz_40 | 41%nat => vz_41 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 58%nat => vz_58 | 59%nat => vz_59 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 60%nat. }
  assert (HR: regs_ok E PaqSE.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaqSE.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaqSE.kn0).
  { unfold know_ok, PaqSE.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K21) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K21) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K21) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K21; lia | clear - HV2l HV2r K3l K3r K11 K21; lia | clear - HV2l HV2r K3l K3r K11 K21; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K6l K6r K8 K11; lia | clear - HV10l HV10r K6l K6r K8 K11; lia | clear - HV10l HV10r K6l K6r K8 K11; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K6l K6r K8 K11; lia | clear - HV10l HV10r K6l K6r K8 K11; lia | clear - HV10l HV10r K6l K6r K8 K11; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r) | clear - HV10l HV10r K6l K6r K8 K11; lia | clear - HV10l HV10r K6l K6r K8 K11; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r) | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV38l HV38r K16l K16r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K16l K16r; lia | clear - HV38l HV38r K16l K16r; lia | clear - HV38l HV38r K16l K16r; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K17l K17r K21) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K18l K18r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K17l K17r K21) | evalEk ZA ltac:(clear - HV40l HV40r K20l K20r) | clear - HV36l HV36r K17l K17r K21; lia | clear - HV36l HV36r K17l K17r K21; lia | byte_tac ltac:(clear - HV40l HV40r K20l K20r) | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K17l K17r K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K21) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaqSE.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaqSE.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 81) <= bv_unsigned a < (vz_2 - 81) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PaqSE.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K21) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K21 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaqSE.ps0) with 0xaf02c in Hms. change (SR.ps_regs PaqSE.ps0) with (map (fun i => (i, nth i PaqSE.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaqSE.ps0) with PaqSE.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaqSE.regs0 PaqSE.regs_out0 60 KS_aqSE KS_aqSE_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaqSE.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaqSE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSE.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaqSE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSE.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaqSE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K21) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K20l K20r) | byte_tac ltac:(clear - HV40l HV40r K20l K20r) | clear; lia].
Qed.

Module PaqSE0 := BndP_Ea_038S8.LibSegEa_aqSE0.
Definition KS_aqSE0 : list nat := Eval vm_compute in (BG.kept_list 60 PaqSE0.regs0 PaqSE0.regs_out0).
Lemma KS_aqSE0_ok : BG.kept_ok 60 PaqSE0.regs0 PaqSE0.regs_out0 KS_aqSE0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma aqSE0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 13) = Z_to_bv 64 (V 58%nat) -> getr R (reg 14) = Z_to_bv 64 (V 59%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1253376 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487264 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 -> 4096 <= (V 10%nat) <= 140737488355272 -> aligned (V 10%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 -> L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> (((V 2%nat) - 96) + 96 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 96)) ->
  L5KA.zeros_at M ((((V 10%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 32) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 10%nat) + 24) (V 38%nat) -> L5.u64_at RSEGS M ((V 10%nat) + 32) (V 38%nat) ->
  0 <= (V 38%nat) <= 140737488355328 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 53%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac52c M) (st fx' R' 0xac5b0 M')
        /\ (forall x, In x KS_aqSE0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 53%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 G2 G8 G10 G11 G12 G13 G14 G21 K0 K1 K2 pvzI19 K4 K5 pvzI20 K7 K8 K9 K10 K11 K12 K13 K14 K15 pvzI21 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV44l; move HV44l before pvzI4; pose proof (proj2 pvzI4) as HV44r; move HV44r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV45l; move HV45l before pvzI5; pose proof (proj2 pvzI5) as HV45r; move HV45r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV46l; move HV46l before pvzI6; pose proof (proj2 pvzI6) as HV46r; move HV46r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV47l; move HV47l before pvzI7; pose proof (proj2 pvzI7) as HV47r; move HV47r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV48l; move HV48l before pvzI8; pose proof (proj2 pvzI8) as HV48r; move HV48r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV49l; move HV49l before pvzI9; pose proof (proj2 pvzI9) as HV49r; move HV49r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV50l; move HV50l before pvzI10; pose proof (proj2 pvzI10) as HV50r; move HV50r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV51l; move HV51l before pvzI11; pose proof (proj2 pvzI11) as HV51r; move HV51r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV52l; move HV52l before pvzI12; pose proof (proj2 pvzI12) as HV52r; move HV52r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV53l; move HV53l before pvzI13; pose proof (proj2 pvzI13) as HV53r; move HV53r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV55l; move HV55l before pvzI14; pose proof (proj2 pvzI14) as HV55r; move HV55r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV56l; move HV56l before pvzI15; pose proof (proj2 pvzI15) as HV56r; move HV56r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV57l; move HV57l before pvzI16; pose proof (proj2 pvzI16) as HV57r; move HV57r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV58l; move HV58l before pvzI17; pose proof (proj2 pvzI17) as HV58r; move HV58r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV59l; move HV59l before pvzI18; pose proof (proj2 pvzI18) as HV59r; move HV59r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K3l; move K3l before pvzI19; pose proof (proj2 pvzI19) as K3r; move K3r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K6l; move K6l before pvzI20; pose proof (proj2 pvzI20) as K6r; move K6r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K16l; move K16l before pvzI21; pose proof (proj2 pvzI21) as K16r; move K16r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *. set (vz_59 := V 59%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 38%nat => Z_to_bv 64 vz_38 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | 59%nat => Z_to_bv 64 vz_59 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 38%nat => vz_38 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | 53%nat => vz_53 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 58%nat => vz_58 | 59%nat => vz_59 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 60%nat. }
  assert (HR: regs_ok E PaqSE0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaqSE0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaqSE0.kn0).
  { unfold know_ok, PaqSE0.kn0.
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
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K6l K6r K8 K11; lia | clear - HV10l HV10r K6l K6r K8 K11; lia | clear - HV10l HV10r K6l K6r K8 K11; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K6l K6r K8 K11; lia | clear - HV10l HV10r K6l K6r K8 K11; lia | clear - HV10l HV10r K6l K6r K8 K11; lia | exactA K12]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K6l K6r K8 K11; lia | clear - HV10l HV10r K6l K6r K8 K11; lia | clear - HV10l HV10r K6l K6r K8 K11; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | evalEk ZA ltac:(clear - HV38l HV38r K16l K16r) | clear - HV10l HV10r K6l K6r K8 K11; lia | clear - HV10l HV10r K6l K6r K8 K11; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11) | evalEk ZA ltac:(clear - HV38l HV38r K16l K16r) | clear - HV10l HV10r K6l K6r K8 K11; lia | clear - HV10l HV10r K6l K6r K8 K11; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K26]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaqSE0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaqSE0.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PaqSE0.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaqSE0.ps0) with 0xac5b0 in Hms. change (SR.ps_regs PaqSE0.ps0) with (map (fun i => (i, nth i PaqSE0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaqSE0.ps0) with PaqSE0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaqSE0.regs0 PaqSE0.regs_out0 60 KS_aqSE0 KS_aqSE0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaqSE0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaqSE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSE0.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaqSE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSE0.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaqSE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSE0.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PaqSE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSE0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaqSE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSE0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaqSE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSE0.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaqSE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSE0.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaqSE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSE0.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PaqSE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSE0.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PaqSE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSE0.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PaqSE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSE0.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PaqSE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PaqSE0.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PaqSE0.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PaqSE1 := BndP_Ea_038S8.LibSegEa_aqSE1.
Definition KS_aqSE1 : list nat := Eval vm_compute in (BG.kept_list 60 PaqSE1.regs0 PaqSE1.regs_out0).
Lemma KS_aqSE1_ok : BG.kept_ok 60 PaqSE1.regs0 PaqSE1.regs_out0 KS_aqSE1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma aqSE1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 13) = Z_to_bv 64 (V 58%nat) -> getr R (reg 14) = Z_to_bv 64 (V 59%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1253376 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487264 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 -> 4096 <= (V 10%nat) <= 140737488355272 -> aligned (V 10%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 -> L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> (((V 2%nat) - 96) + 96 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 96)) ->
  L5KA.zeros_at M ((((V 10%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 32) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 10%nat) + 24) (V 38%nat) -> L5.u64_at RSEGS M ((V 10%nat) + 32) (V 39%nat) ->
  4096 <= (V 38%nat) <= 140737488355328 -> 4120 <= (V 39%nat) <= 140737488355328 -> aligned (V 39%nat) 8 -> 24 <= ((V 39%nat) - (V 38%nat)) <= 100000 ->
  L5.writable RSEGS M ((V 39%nat) - 24) 24 -> (2147446784 + 17592186048512 <= ((V 39%nat) - 24) \/ ((V 39%nat) - 24) + 24 <= 2147446784) -> L5KA.zeros_at M ((((V 39%nat) - 8) / 8) + 2147450880) 1 -> (((V 39%nat) - 24) + 24 <= ((V 2%nat) - 96) \/ ((V 2%nat) - 96) + 96 <= ((V 39%nat) - 24)) ->
  (((V 39%nat) - 24) + 24 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 39%nat) - 24)) -> L5.u64_at RSEGS M ((V 39%nat) - 8) (V 42%nat) -> 0 <= (V 42%nat) <= 18446744073709551614 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 52%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (V 53%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 39%nat) - 8) <= bv_unsigned a < ((V 39%nat) - 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 39%nat) - 8) <= i < ((V 39%nat) - 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac52c M) (st fx' R' 0xac5b0 M')
        /\ (forall x, In x KS_aqSE1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 42%nat) + 1)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 53%nat)
        /\ L5.u64_at RSEGS M' ((V 39%nat) - 8) ((V 42%nat) + 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 pvzI20 G2 G8 G10 G11 G12 G13 G14 G21 K0 K1 K2 pvzI21 K4 K5 pvzI22 K7 K8 K9 K10 K11 K12 K13 K14 K15 pvzI23 pvzI24 K18 pvzI25 K20 K21 K22 K23 K24 K25 pvzI26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV39l; move HV39l before pvzI4; pose proof (proj2 pvzI4) as HV39r; move HV39r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV42l; move HV42l before pvzI5; pose proof (proj2 pvzI5) as HV42r; move HV42r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV44l; move HV44l before pvzI6; pose proof (proj2 pvzI6) as HV44r; move HV44r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV45l; move HV45l before pvzI7; pose proof (proj2 pvzI7) as HV45r; move HV45r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV46l; move HV46l before pvzI8; pose proof (proj2 pvzI8) as HV46r; move HV46r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV47l; move HV47l before pvzI9; pose proof (proj2 pvzI9) as HV47r; move HV47r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV48l; move HV48l before pvzI10; pose proof (proj2 pvzI10) as HV48r; move HV48r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV49l; move HV49l before pvzI11; pose proof (proj2 pvzI11) as HV49r; move HV49r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV50l; move HV50l before pvzI12; pose proof (proj2 pvzI12) as HV50r; move HV50r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV51l; move HV51l before pvzI13; pose proof (proj2 pvzI13) as HV51r; move HV51r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV52l; move HV52l before pvzI14; pose proof (proj2 pvzI14) as HV52r; move HV52r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV53l; move HV53l before pvzI15; pose proof (proj2 pvzI15) as HV53r; move HV53r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV55l; move HV55l before pvzI16; pose proof (proj2 pvzI16) as HV55r; move HV55r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV56l; move HV56l before pvzI17; pose proof (proj2 pvzI17) as HV56r; move HV56r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV57l; move HV57l before pvzI18; pose proof (proj2 pvzI18) as HV57r; move HV57r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV58l; move HV58l before pvzI19; pose proof (proj2 pvzI19) as HV58r; move HV58r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as HV59l; move HV59l before pvzI20; pose proof (proj2 pvzI20) as HV59r; move HV59r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K3l; move K3l before pvzI21; pose proof (proj2 pvzI21) as K3r; move K3r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K6l; move K6l before pvzI22; pose proof (proj2 pvzI22) as K6r; move K6r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K16l; move K16l before pvzI23; pose proof (proj2 pvzI23) as K16r; move K16r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K17l; move K17l before pvzI24; pose proof (proj2 pvzI24) as K17r; move K17r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K19l; move K19l before pvzI25; pose proof (proj2 pvzI25) as K19r; move K19r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K26l; move K26l before pvzI26; pose proof (proj2 pvzI26) as K26r; move K26r before pvzI26; clear pvzI26.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *. set (vz_59 := V 59%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 42%nat => Z_to_bv 64 vz_42 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | 59%nat => Z_to_bv 64 vz_59 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 38%nat => vz_38 | 39%nat => vz_39 | 42%nat => vz_42 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | 53%nat => vz_53 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 58%nat => vz_58 | 59%nat => vz_59 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 60%nat. }
  assert (HR: regs_ok E PaqSE1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaqSE1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaqSE1.kn0).
  { unfold know_ok, PaqSE1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K23; lia | clear - HV2l HV2r K3l K3r K11 K23; lia | clear - HV2l HV2r K3l K3r K11 K23; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11 K24) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11 K24) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11 K24) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11 K24) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K6l K6r K8 K11 K24; lia | clear - HV10l HV10r K6l K6r K8 K11 K24; lia | clear - HV10l HV10r K6l K6r K8 K11 K24; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11 K24) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K6l K6r K8 K11 K24; lia | clear - HV10l HV10r K6l K6r K8 K11 K24; lia | clear - HV10l HV10r K6l K6r K8 K11 K24; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11 K24) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11 K24) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K6l K6r K8 K11 K24; lia | clear - HV10l HV10r K6l K6r K8 K11 K24; lia | clear - HV10l HV10r K6l K6r K8 K11 K24; lia | exactA K12]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11 K24) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K6l K6r K8 K11 K24; lia | clear - HV10l HV10r K6l K6r K8 K11 K24; lia | clear - HV10l HV10r K6l K6r K8 K11 K24; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11 K24) | evalEk ZA ltac:(clear - HV38l HV38r K16l K16r K19l K19r) | clear - HV10l HV10r K6l K6r K8 K11 K24; lia | clear - HV10l HV10r K6l K6r K8 K11 K24; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11 K24) | evalEk ZA ltac:(clear - HV39l HV39r K17l K17r K19l K19r K21 K23 K24) | clear - HV10l HV10r K6l K6r K8 K11 K24; lia | clear - HV10l HV10r K6l K6r K8 K11 K24; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K16l K16r K19l K19r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K17l K17r K19l K19r K21 K23 K24) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV39l HV39r K17l K17r K19l K19r K21 K23 K24) | clear; lia | exact K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K16l K16r K19l K19r HV39l HV39r K17l K17r K21 K23 K24) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV39l HV39r K17l K17r K19l K19r K21 K23 K24) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K17l K17r K19l K19r K21 K23 K24; lia | clear - HV39l HV39r K17l K17r K19l K19r K21 K23 K24; lia | clear - HV39l HV39r K17l K17r K19l K19r K21 K23 K24; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV39l HV39r K17l K17r K19l K19r K21 K23 K24) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV39l HV39r K17l K17r K19l K19r K21 K23 K24) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K17l K17r K19l K19r K21 K23 K24; lia | clear - HV39l HV39r K17l K17r K19l K19r K21 K23 K24; lia | clear - HV39l HV39r K17l K17r K19l K19r K21 K23 K24; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K17l K17r K19l K19r K21 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K17l K17r K19l K19r K21 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11 K24) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV39l HV39r K17l K17r K19l K19r K21 K23 K24) | evalEk ZA ltac:(clear - HV42l HV42r K26l K26r) | clear - HV39l HV39r K17l K17r K19l K19r K21 K23 K24; lia | clear - HV39l HV39r K17l K17r K19l K19r K21 K23 K24; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K26l K26r) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K3l K3r K11 K23; lia | clear - HV2l HV2r K3l K3r K11 K23; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K3l K3r K11 K23; lia | clear - HV2l HV2r K3l K3r K11 K23; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K3l K3r K11 K23; lia | clear - HV2l HV2r K3l K3r K11 K23; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K3l K3r K11 K23; lia | clear - HV2l HV2r K3l K3r K11 K23; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K3l K3r K11 K23; lia | clear - HV2l HV2r K3l K3r K11 K23; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K3l K3r K11 K23; lia | clear - HV2l HV2r K3l K3r K11 K23; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K3l K3r K11 K23; lia | clear - HV2l HV2r K3l K3r K11 K23; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K3l K3r K11 K23; lia | clear - HV2l HV2r K3l K3r K11 K23; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K3l K3r K11 K23; lia | clear - HV2l HV2r K3l K3r K11 K23; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K3l K3r K11 K23; lia | clear - HV2l HV2r K3l K3r K11 K23; lia | exactA K36]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaqSE1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaqSE1.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_39 - 8) <= bv_unsigned a < (vz_39 - 8) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PaqSE1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV39l HV39r K17l K17r K19l K19r K21 K23 K24) | evalEk' ZA Hag ltac:(clear) | clear - HV39l HV39r K17l K17r K19l K19r K21 K23 K24 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaqSE1.ps0) with 0xac5b0 in Hms. change (SR.ps_regs PaqSE1.ps0) with (map (fun i => (i, nth i PaqSE1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaqSE1.ps0) with PaqSE1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaqSE1.regs0 PaqSE1.regs_out0 60 KS_aqSE1 KS_aqSE1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaqSE1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaqSE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSE1.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaqSE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSE1.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaqSE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSE1.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PaqSE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSE1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaqSE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSE1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaqSE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSE1.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaqSE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSE1.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaqSE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSE1.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PaqSE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSE1.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PaqSE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSE1.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PaqSE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSE1.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PaqSE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSE1.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PaqSE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV39l HV39r K17l K17r K19l K19r K21 K23 K24) | evalEk' ZA Hag ltac:(clear - HV42l HV42r K26l K26r) | clear; lia].
Qed.

Module PaqSE1w := BndP_Ea_038S8.LibSegEa_aqSE1w.
Definition KS_aqSE1w : list nat := Eval vm_compute in (BG.kept_list 60 PaqSE1w.regs0 PaqSE1w.regs_out0).
Lemma KS_aqSE1w_ok : BG.kept_ok 60 PaqSE1w.regs0 PaqSE1w.regs_out0 KS_aqSE1w = true. Proof. vm_compute. reflexivity. Qed.
Lemma aqSE1w_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 13) = Z_to_bv 64 (V 58%nat) -> getr R (reg 14) = Z_to_bv 64 (V 59%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1253376 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487264 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 -> 4096 <= (V 10%nat) <= 140737488355272 -> aligned (V 10%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 -> L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> (((V 2%nat) - 96) + 96 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 96)) ->
  L5KA.zeros_at M ((((V 10%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 32) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 10%nat) + 24) (V 38%nat) -> L5.u64_at RSEGS M ((V 10%nat) + 32) (V 39%nat) ->
  4096 <= (V 38%nat) <= 140737488355328 -> 4120 <= (V 39%nat) <= 140737488355328 -> aligned (V 39%nat) 8 -> 24 <= ((V 39%nat) - (V 38%nat)) <= 100000 ->
  L5.writable RSEGS M ((V 39%nat) - 24) 24 -> (2147446784 + 17592186048512 <= ((V 39%nat) - 24) \/ ((V 39%nat) - 24) + 24 <= 2147446784) -> L5KA.zeros_at M ((((V 39%nat) - 8) / 8) + 2147450880) 1 -> (((V 39%nat) - 24) + 24 <= ((V 2%nat) - 96) \/ ((V 2%nat) - 96) + 96 <= ((V 39%nat) - 24)) ->
  (((V 39%nat) - 24) + 24 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 39%nat) - 24)) -> L5.u64_at RSEGS M ((V 39%nat) - 8) 18446744073709551615 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 53%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 39%nat) - 8) <= bv_unsigned a < ((V 39%nat) - 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 39%nat) - 8) <= i < ((V 39%nat) - 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac52c M) (st fx' R' 0xac5b0 M')
        /\ (forall x, In x KS_aqSE1w -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 53%nat)
        /\ L5.u64_at RSEGS M' ((V 39%nat) - 8) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 G2 G8 G10 G11 G12 G13 G14 G21 K0 K1 K2 pvzI20 K4 K5 pvzI21 K7 K8 K9 K10 K11 K12 K13 K14 K15 pvzI22 pvzI23 K18 pvzI24 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV39l; move HV39l before pvzI4; pose proof (proj2 pvzI4) as HV39r; move HV39r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV44l; move HV44l before pvzI5; pose proof (proj2 pvzI5) as HV44r; move HV44r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV45l; move HV45l before pvzI6; pose proof (proj2 pvzI6) as HV45r; move HV45r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV46l; move HV46l before pvzI7; pose proof (proj2 pvzI7) as HV46r; move HV46r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV47l; move HV47l before pvzI8; pose proof (proj2 pvzI8) as HV47r; move HV47r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV48l; move HV48l before pvzI9; pose proof (proj2 pvzI9) as HV48r; move HV48r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV49l; move HV49l before pvzI10; pose proof (proj2 pvzI10) as HV49r; move HV49r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV50l; move HV50l before pvzI11; pose proof (proj2 pvzI11) as HV50r; move HV50r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV51l; move HV51l before pvzI12; pose proof (proj2 pvzI12) as HV51r; move HV51r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV52l; move HV52l before pvzI13; pose proof (proj2 pvzI13) as HV52r; move HV52r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV53l; move HV53l before pvzI14; pose proof (proj2 pvzI14) as HV53r; move HV53r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV55l; move HV55l before pvzI15; pose proof (proj2 pvzI15) as HV55r; move HV55r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV56l; move HV56l before pvzI16; pose proof (proj2 pvzI16) as HV56r; move HV56r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV57l; move HV57l before pvzI17; pose proof (proj2 pvzI17) as HV57r; move HV57r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV58l; move HV58l before pvzI18; pose proof (proj2 pvzI18) as HV58r; move HV58r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV59l; move HV59l before pvzI19; pose proof (proj2 pvzI19) as HV59r; move HV59r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K3l; move K3l before pvzI20; pose proof (proj2 pvzI20) as K3r; move K3r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K6l; move K6l before pvzI21; pose proof (proj2 pvzI21) as K6r; move K6r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K16l; move K16l before pvzI22; pose proof (proj2 pvzI22) as K16r; move K16r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K17l; move K17l before pvzI23; pose proof (proj2 pvzI23) as K17r; move K17r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K19l; move K19l before pvzI24; pose proof (proj2 pvzI24) as K19r; move K19r before pvzI24; clear pvzI24.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *. set (vz_59 := V 59%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | 59%nat => Z_to_bv 64 vz_59 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 38%nat => vz_38 | 39%nat => vz_39 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | 53%nat => vz_53 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 58%nat => vz_58 | 59%nat => vz_59 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 60%nat. }
  assert (HR: regs_ok E PaqSE1w.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaqSE1w.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaqSE1w.kn0).
  { unfold know_ok, PaqSE1w.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K23; lia | clear - HV2l HV2r K3l K3r K11 K23; lia | clear - HV2l HV2r K3l K3r K11 K23; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11 K24) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11 K24) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11 K24) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11 K24) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K6l K6r K8 K11 K24; lia | clear - HV10l HV10r K6l K6r K8 K11 K24; lia | clear - HV10l HV10r K6l K6r K8 K11 K24; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11 K24) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K6l K6r K8 K11 K24; lia | clear - HV10l HV10r K6l K6r K8 K11 K24; lia | clear - HV10l HV10r K6l K6r K8 K11 K24; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11 K24) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11 K24) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K6l K6r K8 K11 K24; lia | clear - HV10l HV10r K6l K6r K8 K11 K24; lia | clear - HV10l HV10r K6l K6r K8 K11 K24; lia | exactA K12]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11 K24) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K6l K6r K8 K11 K24; lia | clear - HV10l HV10r K6l K6r K8 K11 K24; lia | clear - HV10l HV10r K6l K6r K8 K11 K24; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11 K24) | evalEk ZA ltac:(clear - HV38l HV38r K16l K16r K19l K19r) | clear - HV10l HV10r K6l K6r K8 K11 K24; lia | clear - HV10l HV10r K6l K6r K8 K11 K24; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11 K24) | evalEk ZA ltac:(clear - HV39l HV39r K17l K17r K19l K19r K21 K23 K24) | clear - HV10l HV10r K6l K6r K8 K11 K24; lia | clear - HV10l HV10r K6l K6r K8 K11 K24; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K16l K16r K19l K19r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K17l K17r K19l K19r K21 K23 K24) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV39l HV39r K17l K17r K19l K19r K21 K23 K24) | clear; lia | exact K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K16l K16r K19l K19r HV39l HV39r K17l K17r K21 K23 K24) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV39l HV39r K17l K17r K19l K19r K21 K23 K24) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K17l K17r K19l K19r K21 K23 K24; lia | clear - HV39l HV39r K17l K17r K19l K19r K21 K23 K24; lia | clear - HV39l HV39r K17l K17r K19l K19r K21 K23 K24; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV39l HV39r K17l K17r K19l K19r K21 K23 K24) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV39l HV39r K17l K17r K19l K19r K21 K23 K24) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K17l K17r K19l K19r K21 K23 K24; lia | clear - HV39l HV39r K17l K17r K19l K19r K21 K23 K24; lia | clear - HV39l HV39r K17l K17r K19l K19r K21 K23 K24; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K17l K17r K19l K19r K21 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K17l K17r K19l K19r K21 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K6l K6r K8 K11 K24) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV39l HV39r K17l K17r K19l K19r K21 K23 K24) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K17l K17r K19l K19r K21 K23 K24; lia | clear - HV39l HV39r K17l K17r K19l K19r K21 K23 K24; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K3l K3r K11 K23; lia | clear - HV2l HV2r K3l K3r K11 K23; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K3l K3r K11 K23; lia | clear - HV2l HV2r K3l K3r K11 K23; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K3l K3r K11 K23; lia | clear - HV2l HV2r K3l K3r K11 K23; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K3l K3r K11 K23; lia | clear - HV2l HV2r K3l K3r K11 K23; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K3l K3r K11 K23; lia | clear - HV2l HV2r K3l K3r K11 K23; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K3l K3r K11 K23; lia | clear - HV2l HV2r K3l K3r K11 K23; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K3l K3r K11 K23; lia | clear - HV2l HV2r K3l K3r K11 K23; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K3l K3r K11 K23; lia | clear - HV2l HV2r K3l K3r K11 K23; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K3l K3r K11 K23; lia | clear - HV2l HV2r K3l K3r K11 K23; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K3l K3r K11 K23; lia | clear - HV2l HV2r K3l K3r K11 K23; lia | exactA K35]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaqSE1w.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaqSE1w.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_39 - 8) <= bv_unsigned a < (vz_39 - 8) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PaqSE1w.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV39l HV39r K17l K17r K19l K19r K21 K23 K24) | evalEk' ZA Hag ltac:(clear) | clear - HV39l HV39r K17l K17r K19l K19r K21 K23 K24 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaqSE1w.ps0) with 0xac5b0 in Hms. change (SR.ps_regs PaqSE1w.ps0) with (map (fun i => (i, nth i PaqSE1w.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaqSE1w.ps0) with PaqSE1w.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaqSE1w.regs0 PaqSE1w.regs_out0 60 KS_aqSE1w KS_aqSE1w_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaqSE1w.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaqSE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSE1w.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaqSE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSE1w.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaqSE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSE1w.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PaqSE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSE1w.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaqSE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSE1w.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaqSE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSE1w.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaqSE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSE1w.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaqSE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSE1w.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PaqSE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSE1w.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PaqSE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSE1w.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PaqSE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSE1w.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PaqSE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSE1w.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PaqSE1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV39l HV39r K17l K17r K19l K19r K21 K23 K24) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PaqSM0 := BndP_Ea_038S8.LibSegEa_aqSM0.
Definition KS_aqSM0 : list nat := Eval vm_compute in (BG.kept_list 60 PaqSM0.regs0 PaqSM0.regs_out0).
Lemma KS_aqSM0_ok : BG.kept_ok 60 PaqSM0.regs0 PaqSM0.regs_out0 KS_aqSM0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma aqSM0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 13) = Z_to_bv 64 (V 58%nat) -> getr R (reg 14) = Z_to_bv 64 (V 59%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 1 -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 38%nat) ->
  L5.img_clear M 1253376 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487264 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 -> 1 <= (V 36%nat) <= 140737488355326 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac508 M) (st fx' R' 0xac52c M')
        /\ (forall x, In x KS_aqSM0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 36%nat) + 1)
        /\ getr R' (reg 19) = Z_to_bv 64 0
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 36%nat) + 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G8 G9 G10 G11 G12 G13 G14 G18 G19 G20 G21 G22 K0 K1 K2 pvzI10 K4 K5 pvzI11.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV55l; move HV55l before pvzI5; pose proof (proj2 pvzI5) as HV55r; move HV55r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV56l; move HV56l before pvzI6; pose proof (proj2 pvzI6) as HV56r; move HV56r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV57l; move HV57l before pvzI7; pose proof (proj2 pvzI7) as HV57r; move HV57r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV58l; move HV58l before pvzI8; pose proof (proj2 pvzI8) as HV58r; move HV58r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV59l; move HV59l before pvzI9; pose proof (proj2 pvzI9) as HV59r; move HV59r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K6l; move K6l before pvzI11; pose proof (proj2 pvzI11) as K6r; move K6r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *. set (vz_59 := V 59%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | 59%nat => Z_to_bv 64 vz_59 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 36%nat => vz_36 | 38%nat => vz_38 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 58%nat => vz_58 | 59%nat => vz_59 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 60%nat. }
  assert (HR: regs_ok E PaqSM0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaqSM0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaqSM0.kn0).
  { unfold know_ok, PaqSM0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaqSM0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaqSM0.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PaqSM0.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaqSM0.ps0) with 0xac52c in Hms. change (SR.ps_regs PaqSM0.ps0) with (map (fun i => (i, nth i PaqSM0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaqSM0.ps0) with PaqSM0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaqSM0.regs0 PaqSM0.regs_out0 60 KS_aqSM0 KS_aqSM0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaqSM0.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaqSM0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSM0.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaqSM0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PaqSM0.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PaqSM0.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PaqSM1 := BndP_Ea_038S8.LibSegEa_aqSM1.
Definition KS_aqSM1 : list nat := Eval vm_compute in (BG.kept_list 60 PaqSM1.regs0 PaqSM1.regs_out0).
Lemma KS_aqSM1_ok : BG.kept_ok 60 PaqSM1.regs0 PaqSM1.regs_out0 KS_aqSM1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma aqSM1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 13) = Z_to_bv 64 (V 58%nat) -> getr R (reg 14) = Z_to_bv 64 (V 59%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 (V 37%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 38%nat) ->
  L5.img_clear M 1253376 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487264 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 -> 2 <= (V 37%nat) <= 67108864 -> 1 <= (V 36%nat) <= 140737488355326 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac508 M) (st fx' R' 0xac4dc M')
        /\ (forall x, In x KS_aqSM1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 36%nat) + 1)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 37%nat) - 1)
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 36%nat) + 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 G2 G8 G9 G10 G11 G12 G13 G14 G18 G19 G20 G21 G22 K0 K1 K2 pvzI11 K4 K5 pvzI12 pvzI13.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV55l; move HV55l before pvzI6; pose proof (proj2 pvzI6) as HV55r; move HV55r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV56l; move HV56l before pvzI7; pose proof (proj2 pvzI7) as HV56r; move HV56r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV57l; move HV57l before pvzI8; pose proof (proj2 pvzI8) as HV57r; move HV57r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV58l; move HV58l before pvzI9; pose proof (proj2 pvzI9) as HV58r; move HV58r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV59l; move HV59l before pvzI10; pose proof (proj2 pvzI10) as HV59r; move HV59r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K3l; move K3l before pvzI11; pose proof (proj2 pvzI11) as K3r; move K3r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K6l; move K6l before pvzI12; pose proof (proj2 pvzI12) as K6r; move K6r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K7l; move K7l before pvzI13; pose proof (proj2 pvzI13) as K7r; move K7r before pvzI13; clear pvzI13.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *. set (vz_59 := V 59%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | 59%nat => Z_to_bv 64 vz_59 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 58%nat => vz_58 | 59%nat => vz_59 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 60%nat. }
  assert (HR: regs_ok E PaqSM1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaqSM1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaqSM1.kn0).
  { unfold know_ok, PaqSM1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaqSM1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaqSM1.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PaqSM1.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaqSM1.ps0) with 0xac4dc in Hms. change (SR.ps_regs PaqSM1.ps0) with (map (fun i => (i, nth i PaqSM1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaqSM1.ps0) with PaqSM1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaqSM1.regs0 PaqSM1.regs_out0 60 KS_aqSM1 KS_aqSM1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaqSM1.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaqSM1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSM1.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaqSM1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PaqSM1.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PaqSM1.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PaqSR := BndP_Ea_038S8.LibSegEa_aqSR.
Definition KS_aqSR : list nat := Eval vm_compute in (BG.kept_list 60 PaqSR.regs0 PaqSR.regs_out0).
Lemma KS_aqSR_ok : BG.kept_ok 60 PaqSR.regs0 PaqSR.regs_out0 KS_aqSR = true. Proof. vm_compute. reflexivity. Qed.
Lemma aqSR_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 13) = Z_to_bv 64 (V 58%nat) -> getr R (reg 14) = Z_to_bv 64 (V 59%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1253376 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487264 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 53%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac4a4 M) (st fx' R' 0xac5b0 M')
        /\ (forall x, In x KS_aqSR -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 53%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 G2 G8 G10 G11 G12 G13 G14 G21 K0 K1 K2 pvzI18 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV44l; move HV44l before pvzI3; pose proof (proj2 pvzI3) as HV44r; move HV44r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV45l; move HV45l before pvzI4; pose proof (proj2 pvzI4) as HV45r; move HV45r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV46l; move HV46l before pvzI5; pose proof (proj2 pvzI5) as HV46r; move HV46r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV47l; move HV47l before pvzI6; pose proof (proj2 pvzI6) as HV47r; move HV47r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV48l; move HV48l before pvzI7; pose proof (proj2 pvzI7) as HV48r; move HV48r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV49l; move HV49l before pvzI8; pose proof (proj2 pvzI8) as HV49r; move HV49r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV50l; move HV50l before pvzI9; pose proof (proj2 pvzI9) as HV50r; move HV50r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV51l; move HV51l before pvzI10; pose proof (proj2 pvzI10) as HV51r; move HV51r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV52l; move HV52l before pvzI11; pose proof (proj2 pvzI11) as HV52r; move HV52r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV53l; move HV53l before pvzI12; pose proof (proj2 pvzI12) as HV53r; move HV53r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV55l; move HV55l before pvzI13; pose proof (proj2 pvzI13) as HV55r; move HV55r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV56l; move HV56l before pvzI14; pose proof (proj2 pvzI14) as HV56r; move HV56r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV57l; move HV57l before pvzI15; pose proof (proj2 pvzI15) as HV57r; move HV57r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV58l; move HV58l before pvzI16; pose proof (proj2 pvzI16) as HV58r; move HV58r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV59l; move HV59l before pvzI17; pose proof (proj2 pvzI17) as HV59r; move HV59r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K3l; move K3l before pvzI18; pose proof (proj2 pvzI18) as K3r; move K3r before pvzI18; clear pvzI18.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *. set (vz_59 := V 59%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | 59%nat => Z_to_bv 64 vz_59 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | 53%nat => vz_53 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 58%nat => vz_58 | 59%nat => vz_59 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 60%nat. }
  assert (HR: regs_ok E PaqSR.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaqSR.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaqSR.kn0).
  { unfold know_ok, PaqSR.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K15]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaqSR.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaqSR.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PaqSR.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaqSR.ps0) with 0xac5b0 in Hms. change (SR.ps_regs PaqSR.ps0) with (map (fun i => (i, nth i PaqSR.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaqSR.ps0) with PaqSR.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaqSR.regs0 PaqSR.regs_out0 60 KS_aqSR KS_aqSR_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaqSR.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaqSR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSR.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaqSR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSR.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaqSR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSR.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PaqSR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSR.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaqSR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSR.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaqSR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSR.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaqSR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSR.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PaqSR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSR.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PaqSR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSR.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PaqSR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaqSR.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PaqSR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PaqSR.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PaqSR.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

End PEAENCSTP.
