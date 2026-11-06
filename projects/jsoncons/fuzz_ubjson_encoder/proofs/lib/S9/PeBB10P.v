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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.seg Require BndP_Eb_000S9 BndP_Eb_001S9.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PMBB10P.
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

Module Pab10E := BndP_Eb_000S9.LibSegEb_ab10E.
Definition KS_ab10E_0 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10E.regs0 Pab10E.regs_out0).
Lemma KS_ab10E_0_ok : BG.kept_ok 60 Pab10E.regs0 Pab10E.regs_out0 KS_ab10E_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10E_1 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10E.regs0 Pab10E.regs_out1).
Lemma KS_ab10E_1_ok : BG.kept_ok 60 Pab10E.regs0 Pab10E.regs_out1 KS_ab10E_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ab10E_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 35%nat) ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487184 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 16) 16 -> 1 <= (V 33%nat) <= 140737488355328 -> 0 <= (V 35%nat) <= 67108863 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 8) <= bv_unsigned a < ((V 2%nat) - 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 8) <= i < ((V 2%nat) - 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xbaa14 M) (st fx' R' 0xbab60 M')
        /\ (forall x, In x KS_ab10E_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 16)
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat))
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ (((V 35%nat) - 0) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))
      \/ (msteps RSEGS (st fx R 0xbaa14 M) (st fx' R' 0xbaa70 M')
        /\ (forall x, In x KS_ab10E_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 16)
        /\ getr R' (reg 5) = Z_to_bv 64 13
        /\ getr R' (reg 6) = Z_to_bv 64 2147450880
        /\ getr R' (reg 7) = Z_to_bv 64 8185
        /\ getr R' (reg 11) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat))
        /\ getr R' (reg 14) = Z_to_bv 64 5
        /\ getr R' (reg 15) = Z_to_bv 64 10
        /\ getr R' (reg 16) = Z_to_bv 64 2
        /\ getr R' (reg 17) = Z_to_bv 64 1
        /\ getr R' (reg 28) = Z_to_bv 64 146496
        /\ 1 <= (((V 35%nat) - 0) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G10 G11 K0 K1 K2 pvzI4 K4 K5 pvzI5 pvzI6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K3l; move K3l before pvzI4; pose proof (proj2 pvzI4) as K3r; move K3r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K6l; move K6l before pvzI5; pose proof (proj2 pvzI5) as K6r; move K6r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K7l; move K7l before pvzI6; pose proof (proj2 pvzI6) as K7r; move K7r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 36%nat. }
  assert (HR: regs_ok E Pab10E.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pab10E.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pab10E.kn0).
  { unfold know_ok, Pab10E.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pab10E.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pab10E.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 8) <= bv_unsigned a < (vz_2 - 8) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pab10E.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc Pab10E.ps0) with 0xbab60 in Hms. change (SR.ps_regs Pab10E.ps0) with (map (fun i => (i, nth i Pab10E.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10E.ps0) with Pab10E.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10E.regs0 Pab10E.regs_out0 60 KS_ab10E_0 KS_ab10E_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10E.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth Pab10E.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10E.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10E.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10E.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10E.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10E.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pab10E.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10E.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth Pab10E.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
  - right.
    change (SR.ps_pc Pab10E.ps1) with 0xbaa70 in Hms. change (SR.ps_regs Pab10E.ps1) with (map (fun i => (i, nth i Pab10E.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10E.ps1) with Pab10E.cells1 in Hcells. unfold Pab10E.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10E.regs0 Pab10E.regs_out1 60 KS_ab10E_1 KS_ab10E_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10E.regs_out1 E' R' 2 Hregs) by (clear; lia). cbn [nth Pab10E.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10E.regs_out1 E' R' 5 Hregs) by (clear; lia). cbn [nth Pab10E.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10E.regs_out1 E' R' 6 Hregs) by (clear; lia). cbn [nth Pab10E.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10E.regs_out1 E' R' 7 Hregs) by (clear; lia). cbn [nth Pab10E.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10E.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth Pab10E.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10E.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10E.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10E.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth Pab10E.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10E.regs_out1 E' R' 14 Hregs) by (clear; lia). cbn [nth Pab10E.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10E.regs_out1 E' R' 15 Hregs) by (clear; lia). cbn [nth Pab10E.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10E.regs_out1 E' R' 16 Hregs) by (clear; lia). cbn [nth Pab10E.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10E.regs_out1 E' R' 17 Hregs) by (clear; lia). cbn [nth Pab10E.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10E.regs_out1 E' R' 28 Hregs) by (clear; lia). cbn [nth Pab10E.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module Pab10E00 := BndP_Eb_000S9.LibSegEb_ab10E00.
Definition KS_ab10E00 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10E00.regs0 Pab10E00.regs_out0).
Lemma KS_ab10E00_ok : BG.kept_ok 60 Pab10E00.regs0 Pab10E00.regs_out0 KS_ab10E00 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ab10E00_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 35%nat) ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487184 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 16) 16 -> 0 <= (V 33%nat) <= 0 -> 0 <= (V 35%nat) <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 8) <= bv_unsigned a < ((V 2%nat) - 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 8) <= i < ((V 2%nat) - 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xbaa14 M) (st fx' R' 0xbab60 M')
        /\ (forall x, In x KS_ab10E00 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 16)
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G10 G11 K0 K1 K2 pvzI4 K4 K5 pvzI5 pvzI6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K3l; move K3l before pvzI4; pose proof (proj2 pvzI4) as K3r; move K3r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K6l; move K6l before pvzI5; pose proof (proj2 pvzI5) as K6r; move K6r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K7l; move K7l before pvzI6; pose proof (proj2 pvzI6) as K7r; move K7r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 36%nat. }
  assert (HR: regs_ok E Pab10E00.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pab10E00.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pab10E00.kn0).
  { unfold know_ok, Pab10E00.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pab10E00.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pab10E00.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 8) <= bv_unsigned a < (vz_2 - 8) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pab10E00.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pab10E00.ps0) with 0xbab60 in Hms. change (SR.ps_regs Pab10E00.ps0) with (map (fun i => (i, nth i Pab10E00.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pab10E00.ps0) with Pab10E00.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10E00.regs0 Pab10E00.regs_out0 60 KS_ab10E00 KS_ab10E00_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pab10E00.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth Pab10E00.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pab10E00.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10E00.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pab10E00.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10E00.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pab10E00.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pab10E00.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pab10E00.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth Pab10E00.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module Pab10BZ := BndP_Eb_000S9.LibSegEb_ab10BZ.
Definition KS_ab10BZ_0 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10BZ.regs0 Pab10BZ.regs_out0).
Lemma KS_ab10BZ_0_ok : BG.kept_ok 60 Pab10BZ.regs0 Pab10BZ.regs_out0 KS_ab10BZ_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10BZ_1 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10BZ.regs0 Pab10BZ.regs_out1).
Lemma KS_ab10BZ_1_ok : BG.kept_ok 60 Pab10BZ.regs0 Pab10BZ.regs_out1 KS_ab10BZ_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10BZ_2 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10BZ.regs0 Pab10BZ.regs_out2).
Lemma KS_ab10BZ_2_ok : BG.kept_ok 60 Pab10BZ.regs0 Pab10BZ.regs_out2 KS_ab10BZ_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10BZ_3 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10BZ.regs0 Pab10BZ.regs_out3).
Lemma KS_ab10BZ_3_ok : BG.kept_ok 60 Pab10BZ.regs0 Pab10BZ.regs_out3 KS_ab10BZ_3 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10BZ_4 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10BZ.regs0 Pab10BZ.regs_out4).
Lemma KS_ab10BZ_4_ok : BG.kept_ok 60 Pab10BZ.regs0 Pab10BZ.regs_out4 KS_ab10BZ_4 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10BZ_5 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10BZ.regs0 Pab10BZ.regs_out5).
Lemma KS_ab10BZ_5_ok : BG.kept_ok 60 Pab10BZ.regs0 Pab10BZ.regs_out5 KS_ab10BZ_5 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10BZ_6 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10BZ.regs0 Pab10BZ.regs_out6).
Lemma KS_ab10BZ_6_ok : BG.kept_ok 60 Pab10BZ.regs0 Pab10BZ.regs_out6 KS_ab10BZ_6 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10BZ_7 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10BZ.regs0 Pab10BZ.regs_out7).
Lemma KS_ab10BZ_7_ok : BG.kept_ok 60 Pab10BZ.regs0 Pab10BZ.regs_out7 KS_ab10BZ_7 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ab10BZ_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 16) -> getr R (reg 5) = Z_to_bv 64 13 -> getr R (reg 6) = Z_to_bv 64 2147450880 -> getr R (reg 7) = Z_to_bv 64 8185 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 (V 36%nat) -> getr R (reg 13) = Z_to_bv 64 (V 34%nat) -> getr R (reg 14) = Z_to_bv 64 5 -> getr R (reg 15) = Z_to_bv 64 10 -> getr R (reg 16) = Z_to_bv 64 2 -> getr R (reg 17) = Z_to_bv 64 1 -> getr R (reg 28) = Z_to_bv 64 146496 ->
  1 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 34%nat) <= 140737488355328 -> 0 <= (V 36%nat) <= 18446744073709551615 -> L5.u8_at RSEGS M (V 33%nat) (V 37%nat) ->
  0 <= (V 37%nat) <= 255 -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab1c M')
        /\ (forall x, In x KS_ab10BZ_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 5
        /\ (((V 37%nat) + 18446744073709551568) mod 2 ^ 64) < 10
        /\ (((V 36%nat) - 5) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab60 M')
        /\ (forall x, In x KS_ab10BZ_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 37%nat) - 48)
        /\ 10 <= (((V 37%nat) + 18446744073709551568) mod 2 ^ 64)
        /\ (((V 36%nat) - 5) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab1c M')
        /\ (forall x, In x KS_ab10BZ_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 5
        /\ (((V 37%nat) + 18446744073709551568) mod 2 ^ 64) < 10
        /\ (((V 36%nat) - 1) mod 2 ^ 64) < 1
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab60 M')
        /\ (forall x, In x KS_ab10BZ_3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 37%nat) - 48)
        /\ 10 <= (((V 37%nat) + 18446744073709551568) mod 2 ^ 64)
        /\ (((V 36%nat) - 1) mod 2 ^ 64) < 1
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab60 M')
        /\ (forall x, In x KS_ab10BZ_4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ bv_unsigned (getr R' (reg 12)) = (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255)
        /\ bv_unsigned (getr R' (reg 29)) = (Z.land (8185 / 2 ^ ((((V 37%nat) + 18446744073709551571) mod 2 ^ 64) mod 64)) 1)
        /\ (((Z.land (8185 / 2 ^ ((((V 37%nat) + 18446744073709551571) mod 2 ^ 64) mod 64)) 1) - 0) mod 2 ^ 64) < 1
        /\ (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255) < 13
        /\ (((V 36%nat) - 0) mod 2 ^ 64) < 1
        /\ 1 <= (((V 36%nat) - 1) mod 2 ^ 64)
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbaab4 M')
        /\ (forall x, In x KS_ab10BZ_5 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 12)) = ((((4 * (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255)) mod 2 ^ 64) + 146496) mod 2 ^ 64)
        /\ bv_unsigned (getr R' (reg 29)) = (Z.land (8185 / 2 ^ ((((V 37%nat) + 18446744073709551571) mod 2 ^ 64) mod 64)) 1)
        /\ 1 <= (((Z.land (8185 / 2 ^ ((((V 37%nat) + 18446744073709551571) mod 2 ^ 64) mod 64)) 1) - 0) mod 2 ^ 64)
        /\ (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255) < 13
        /\ (((V 36%nat) - 0) mod 2 ^ 64) < 1
        /\ 1 <= (((V 36%nat) - 1) mod 2 ^ 64)
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab60 M')
        /\ (forall x, In x KS_ab10BZ_6 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ bv_unsigned (getr R' (reg 12)) = (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255)
        /\ getr R' (reg 29) = Z_to_bv 64 ((V 37%nat) - 45)
        /\ 13 <= (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255)
        /\ (((V 36%nat) - 0) mod 2 ^ 64) < 1
        /\ 1 <= (((V 36%nat) - 1) mod 2 ^ 64)
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab1c M')
        /\ (forall x, In x KS_ab10BZ_7 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ 1 <= (((V 36%nat) - 0) mod 2 ^ 64)
        /\ 1 <= (((V 36%nat) - 1) mod 2 ^ 64)
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G5 G6 G7 G10 G11 G12 G13 G14 G15 G16 G17 G28 pvzI6 pvzI7 pvzI8 K3 pvzI9 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K1l; move K1l before pvzI7; pose proof (proj2 pvzI7) as K1r; move K1r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K2l; move K2l before pvzI8; pose proof (proj2 pvzI8) as K2r; move K2r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K4l; move K4l before pvzI9; pose proof (proj2 pvzI9) as K4r; move K4r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E Pab10BZ.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pab10BZ.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pab10BZ.kn0).
  { unfold know_ok, Pab10BZ.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K1l K1r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K2l K2r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r) | evalEk ZA ltac:(clear - HV37l HV37r K4l K4r) | clear - HV33l HV33r K0l K0r; lia | clear - HV33l HV33r K0l K0r; lia | byte_tac ltac:(clear - HV37l HV37r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r; lia | clear - HV33l HV33r K0l K0r; lia | clear - HV33l HV33r K0l K0r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pab10BZ.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pab10BZ.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pab10BZ.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc Pab10BZ.ps0) with 0xbab1c in Hms. change (SR.ps_regs Pab10BZ.ps0) with (map (fun i => (i, nth i Pab10BZ.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10BZ.ps0) with Pab10BZ.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10BZ.regs0 Pab10BZ.regs_out0 60 KS_ab10BZ_0 KS_ab10BZ_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10BZ.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10BZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10BZ.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pab10BZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10BZ.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10BZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. left.
    change (SR.ps_pc Pab10BZ.ps1) with 0xbab60 in Hms. change (SR.ps_regs Pab10BZ.ps1) with (map (fun i => (i, nth i Pab10BZ.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10BZ.ps1) with Pab10BZ.cells1 in Hcells. unfold Pab10BZ.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10BZ.regs0 Pab10BZ.regs_out1 60 KS_ab10BZ_1 KS_ab10BZ_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10BZ.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10BZ.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10BZ.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10BZ.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. left.
    change (SR.ps_pc Pab10BZ.ps2) with 0xbab1c in Hms. change (SR.ps_regs Pab10BZ.ps2) with (map (fun i => (i, nth i Pab10BZ.regs_out2 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10BZ.ps2) with Pab10BZ.cells2 in Hcells. unfold Pab10BZ.cells2 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10BZ.regs0 Pab10BZ.regs_out2 60 KS_ab10BZ_2 KS_ab10BZ_2_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10BZ.regs_out2 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10BZ.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10BZ.regs_out2 E' R' 11 Hregs) by (clear; lia). cbn [nth Pab10BZ.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10BZ.regs_out2 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10BZ.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. left.
    change (SR.ps_pc Pab10BZ.ps3) with 0xbab60 in Hms. change (SR.ps_regs Pab10BZ.ps3) with (map (fun i => (i, nth i Pab10BZ.regs_out3 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10BZ.ps3) with Pab10BZ.cells3 in Hcells. unfold Pab10BZ.cells3 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10BZ.regs0 Pab10BZ.regs_out3 60 KS_ab10BZ_3 KS_ab10BZ_3_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10BZ.regs_out3 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10BZ.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10BZ.regs_out3 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10BZ.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. left.
    change (SR.ps_pc Pab10BZ.ps4) with 0xbab60 in Hms. change (SR.ps_regs Pab10BZ.ps4) with (map (fun i => (i, nth i Pab10BZ.regs_out4 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10BZ.ps4) with Pab10BZ.cells4 in Hcells. unfold Pab10BZ.cells4 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10BZ.regs0 Pab10BZ.regs_out4 60 KS_ab10BZ_4 KS_ab10BZ_4_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10BZ.regs_out4 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10BZ.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10BZ.regs_out4 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10BZ.regs_out4]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg Pab10BZ.regs_out4 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10BZ.regs_out4]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. left.
    change (SR.ps_pc Pab10BZ.ps5) with 0xbaab4 in Hms. change (SR.ps_regs Pab10BZ.ps5) with (map (fun i => (i, nth i Pab10BZ.regs_out5 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10BZ.ps5) with Pab10BZ.cells5 in Hcells. unfold Pab10BZ.cells5 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10BZ.regs0 Pab10BZ.regs_out5 60 KS_ab10BZ_5 KS_ab10BZ_5_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10BZ.regs_out5 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10BZ.regs_out5]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg Pab10BZ.regs_out5 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10BZ.regs_out5]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. left.
    change (SR.ps_pc Pab10BZ.ps6) with 0xbab60 in Hms. change (SR.ps_regs Pab10BZ.ps6) with (map (fun i => (i, nth i Pab10BZ.regs_out6 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10BZ.ps6) with Pab10BZ.cells6 in Hcells. unfold Pab10BZ.cells6 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10BZ.regs0 Pab10BZ.regs_out6 60 KS_ab10BZ_6 KS_ab10BZ_6_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10BZ.regs_out6 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10BZ.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10BZ.regs_out6 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10BZ.regs_out6]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg Pab10BZ.regs_out6 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10BZ.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right.
    change (SR.ps_pc Pab10BZ.ps7) with 0xbab1c in Hms. change (SR.ps_regs Pab10BZ.ps7) with (map (fun i => (i, nth i Pab10BZ.regs_out7 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10BZ.ps7) with Pab10BZ.cells7 in Hcells. unfold Pab10BZ.cells7 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10BZ.regs0 Pab10BZ.regs_out7 60 KS_ab10BZ_7 KS_ab10BZ_7_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10BZ.regs_out7 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10BZ.regs_out7]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10BZ.regs_out7 E' R' 11 Hregs) by (clear; lia). cbn [nth Pab10BZ.regs_out7]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.

Module Pab10P1 := BndP_Eb_000S9.LibSegEb_ab10P1.
Definition KS_ab10P1_0 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P1.regs0 Pab10P1.regs_out0).
Lemma KS_ab10P1_0_ok : BG.kept_ok 60 Pab10P1.regs0 Pab10P1.regs_out0 KS_ab10P1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P1_1 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P1.regs0 Pab10P1.regs_out1).
Lemma KS_ab10P1_1_ok : BG.kept_ok 60 Pab10P1.regs0 Pab10P1.regs_out1 KS_ab10P1_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P1_2 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P1.regs0 Pab10P1.regs_out2).
Lemma KS_ab10P1_2_ok : BG.kept_ok 60 Pab10P1.regs0 Pab10P1.regs_out2 KS_ab10P1_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P1_3 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P1.regs0 Pab10P1.regs_out3).
Lemma KS_ab10P1_3_ok : BG.kept_ok 60 Pab10P1.regs0 Pab10P1.regs_out3 KS_ab10P1_3 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P1_4 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P1.regs0 Pab10P1.regs_out4).
Lemma KS_ab10P1_4_ok : BG.kept_ok 60 Pab10P1.regs0 Pab10P1.regs_out4 KS_ab10P1_4 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P1_5 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P1.regs0 Pab10P1.regs_out5).
Lemma KS_ab10P1_5_ok : BG.kept_ok 60 Pab10P1.regs0 Pab10P1.regs_out5 KS_ab10P1_5 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P1_6 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P1.regs0 Pab10P1.regs_out6).
Lemma KS_ab10P1_6_ok : BG.kept_ok 60 Pab10P1.regs0 Pab10P1.regs_out6 KS_ab10P1_6 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P1_7 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P1.regs0 Pab10P1.regs_out7).
Lemma KS_ab10P1_7_ok : BG.kept_ok 60 Pab10P1.regs0 Pab10P1.regs_out7 KS_ab10P1_7 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ab10P1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 16) -> getr R (reg 5) = Z_to_bv 64 13 -> getr R (reg 6) = Z_to_bv 64 2147450880 -> getr R (reg 7) = Z_to_bv 64 8185 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 (V 36%nat) -> getr R (reg 13) = Z_to_bv 64 (V 34%nat) -> getr R (reg 14) = Z_to_bv 64 5 -> getr R (reg 15) = Z_to_bv 64 10 -> getr R (reg 16) = Z_to_bv 64 2 -> getr R (reg 17) = Z_to_bv 64 1 -> getr R (reg 28) = Z_to_bv 64 146496 ->
  1 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 34%nat) <= 140737488355328 -> 0 <= (V 36%nat) <= 18446744073709551615 -> L5.u8_at RSEGS M (V 33%nat) (V 37%nat) ->
  0 <= (V 37%nat) <= 255 -> L5.u8_at RSEGS M (((V 33%nat) / 8) + 2147450880) 1 -> 0 <= Z.land (V 33%nat) 7 <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab1c M')
        /\ (forall x, In x KS_ab10P1_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 5
        /\ getr R' (reg 29) = Z_to_bv 64 0
        /\ (((V 37%nat) + 18446744073709551568) mod 2 ^ 64) < 10
        /\ (((V 36%nat) - 5) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab60 M')
        /\ (forall x, In x KS_ab10P1_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 37%nat) - 48)
        /\ getr R' (reg 29) = Z_to_bv 64 0
        /\ 10 <= (((V 37%nat) + 18446744073709551568) mod 2 ^ 64)
        /\ (((V 36%nat) - 5) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab1c M')
        /\ (forall x, In x KS_ab10P1_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 5
        /\ getr R' (reg 29) = Z_to_bv 64 0
        /\ (((V 37%nat) + 18446744073709551568) mod 2 ^ 64) < 10
        /\ (((V 36%nat) - 1) mod 2 ^ 64) < 1
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab60 M')
        /\ (forall x, In x KS_ab10P1_3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 37%nat) - 48)
        /\ getr R' (reg 29) = Z_to_bv 64 0
        /\ 10 <= (((V 37%nat) + 18446744073709551568) mod 2 ^ 64)
        /\ (((V 36%nat) - 1) mod 2 ^ 64) < 1
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab60 M')
        /\ (forall x, In x KS_ab10P1_4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ bv_unsigned (getr R' (reg 12)) = (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255)
        /\ bv_unsigned (getr R' (reg 29)) = (Z.land (8185 / 2 ^ ((((V 37%nat) + 18446744073709551571) mod 2 ^ 64) mod 64)) 1)
        /\ (((Z.land (8185 / 2 ^ ((((V 37%nat) + 18446744073709551571) mod 2 ^ 64) mod 64)) 1) - 0) mod 2 ^ 64) < 1
        /\ (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255) < 13
        /\ (((V 36%nat) - 0) mod 2 ^ 64) < 1
        /\ 1 <= (((V 36%nat) - 1) mod 2 ^ 64)
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbaab4 M')
        /\ (forall x, In x KS_ab10P1_5 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 12)) = ((((4 * (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255)) mod 2 ^ 64) + 146496) mod 2 ^ 64)
        /\ bv_unsigned (getr R' (reg 29)) = (Z.land (8185 / 2 ^ ((((V 37%nat) + 18446744073709551571) mod 2 ^ 64) mod 64)) 1)
        /\ 1 <= (((Z.land (8185 / 2 ^ ((((V 37%nat) + 18446744073709551571) mod 2 ^ 64) mod 64)) 1) - 0) mod 2 ^ 64)
        /\ (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255) < 13
        /\ (((V 36%nat) - 0) mod 2 ^ 64) < 1
        /\ 1 <= (((V 36%nat) - 1) mod 2 ^ 64)
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab60 M')
        /\ (forall x, In x KS_ab10P1_6 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ bv_unsigned (getr R' (reg 12)) = (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255)
        /\ getr R' (reg 29) = Z_to_bv 64 ((V 37%nat) - 45)
        /\ 13 <= (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255)
        /\ (((V 36%nat) - 0) mod 2 ^ 64) < 1
        /\ 1 <= (((V 36%nat) - 1) mod 2 ^ 64)
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab1c M')
        /\ (forall x, In x KS_ab10P1_7 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ 1 <= (((V 36%nat) - 0) mod 2 ^ 64)
        /\ 1 <= (((V 36%nat) - 1) mod 2 ^ 64)
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G5 G6 G7 G10 G11 G12 G13 G14 G15 G16 G17 G28 pvzI6 pvzI7 pvzI8 K3 pvzI9 K5 pvzI10.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K1l; move K1l before pvzI7; pose proof (proj2 pvzI7) as K1r; move K1r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K2l; move K2l before pvzI8; pose proof (proj2 pvzI8) as K2r; move K2r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K4l; move K4l before pvzI9; pose proof (proj2 pvzI9) as K4r; move K4r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E Pab10P1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pab10P1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pab10P1.kn0).
  { unfold know_ok, Pab10P1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K6l K6r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K1l K1r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K2l K2r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K6l K6r) | evalEk ZA ltac:(clear - HV37l HV37r K4l K4r) | clear - HV33l HV33r K0l K0r K6l K6r; lia | clear - HV33l HV33r K0l K0r K6l K6r; lia | byte_tac ltac:(clear - HV37l HV37r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K6l K6r; lia | clear - HV33l HV33r K0l K0r K6l K6r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K6l K6r) | clear; lia | exact (conj K6l K6r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pab10P1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pab10P1.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pab10P1.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc Pab10P1.ps0) with 0xbab1c in Hms. change (SR.ps_regs Pab10P1.ps0) with (map (fun i => (i, nth i Pab10P1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P1.ps0) with Pab10P1.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P1.regs0 Pab10P1.regs_out0 60 KS_ab10P1_0 KS_ab10P1_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pab10P1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P1.regs_out0 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. left.
    change (SR.ps_pc Pab10P1.ps1) with 0xbab60 in Hms. change (SR.ps_regs Pab10P1.ps1) with (map (fun i => (i, nth i Pab10P1.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P1.ps1) with Pab10P1.cells1 in Hcells. unfold Pab10P1.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P1.regs0 Pab10P1.regs_out1 60 KS_ab10P1_1 KS_ab10P1_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P1.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P1.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P1.regs_out1 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. left.
    change (SR.ps_pc Pab10P1.ps2) with 0xbab1c in Hms. change (SR.ps_regs Pab10P1.ps2) with (map (fun i => (i, nth i Pab10P1.regs_out2 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P1.ps2) with Pab10P1.cells2 in Hcells. unfold Pab10P1.cells2 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P1.regs0 Pab10P1.regs_out2 60 KS_ab10P1_2 KS_ab10P1_2_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P1.regs_out2 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P1.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P1.regs_out2 E' R' 11 Hregs) by (clear; lia). cbn [nth Pab10P1.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P1.regs_out2 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P1.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P1.regs_out2 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P1.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. left.
    change (SR.ps_pc Pab10P1.ps3) with 0xbab60 in Hms. change (SR.ps_regs Pab10P1.ps3) with (map (fun i => (i, nth i Pab10P1.regs_out3 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P1.ps3) with Pab10P1.cells3 in Hcells. unfold Pab10P1.cells3 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P1.regs0 Pab10P1.regs_out3 60 KS_ab10P1_3 KS_ab10P1_3_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P1.regs_out3 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P1.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P1.regs_out3 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P1.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P1.regs_out3 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P1.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. left.
    change (SR.ps_pc Pab10P1.ps4) with 0xbab60 in Hms. change (SR.ps_regs Pab10P1.ps4) with (map (fun i => (i, nth i Pab10P1.regs_out4 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P1.ps4) with Pab10P1.cells4 in Hcells. unfold Pab10P1.cells4 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P1.regs0 Pab10P1.regs_out4 60 KS_ab10P1_4 KS_ab10P1_4_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P1.regs_out4 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P1.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P1.regs_out4 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P1.regs_out4]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg Pab10P1.regs_out4 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P1.regs_out4]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. left.
    change (SR.ps_pc Pab10P1.ps5) with 0xbaab4 in Hms. change (SR.ps_regs Pab10P1.ps5) with (map (fun i => (i, nth i Pab10P1.regs_out5 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P1.ps5) with Pab10P1.cells5 in Hcells. unfold Pab10P1.cells5 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P1.regs0 Pab10P1.regs_out5 60 KS_ab10P1_5 KS_ab10P1_5_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P1.regs_out5 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P1.regs_out5]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg Pab10P1.regs_out5 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P1.regs_out5]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. left.
    change (SR.ps_pc Pab10P1.ps6) with 0xbab60 in Hms. change (SR.ps_regs Pab10P1.ps6) with (map (fun i => (i, nth i Pab10P1.regs_out6 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P1.ps6) with Pab10P1.cells6 in Hcells. unfold Pab10P1.cells6 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P1.regs0 Pab10P1.regs_out6 60 KS_ab10P1_6 KS_ab10P1_6_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P1.regs_out6 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P1.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P1.regs_out6 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P1.regs_out6]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg Pab10P1.regs_out6 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P1.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right.
    change (SR.ps_pc Pab10P1.ps7) with 0xbab1c in Hms. change (SR.ps_regs Pab10P1.ps7) with (map (fun i => (i, nth i Pab10P1.regs_out7 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P1.ps7) with Pab10P1.cells7 in Hcells. unfold Pab10P1.cells7 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P1.regs0 Pab10P1.regs_out7 60 KS_ab10P1_7 KS_ab10P1_7_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P1.regs_out7 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P1.regs_out7]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P1.regs_out7 E' R' 11 Hregs) by (clear; lia). cbn [nth Pab10P1.regs_out7]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.

Module Pab10P2 := BndP_Eb_000S9.LibSegEb_ab10P2.
Definition KS_ab10P2_0 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P2.regs0 Pab10P2.regs_out0).
Lemma KS_ab10P2_0_ok : BG.kept_ok 60 Pab10P2.regs0 Pab10P2.regs_out0 KS_ab10P2_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P2_1 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P2.regs0 Pab10P2.regs_out1).
Lemma KS_ab10P2_1_ok : BG.kept_ok 60 Pab10P2.regs0 Pab10P2.regs_out1 KS_ab10P2_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P2_2 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P2.regs0 Pab10P2.regs_out2).
Lemma KS_ab10P2_2_ok : BG.kept_ok 60 Pab10P2.regs0 Pab10P2.regs_out2 KS_ab10P2_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P2_3 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P2.regs0 Pab10P2.regs_out3).
Lemma KS_ab10P2_3_ok : BG.kept_ok 60 Pab10P2.regs0 Pab10P2.regs_out3 KS_ab10P2_3 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P2_4 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P2.regs0 Pab10P2.regs_out4).
Lemma KS_ab10P2_4_ok : BG.kept_ok 60 Pab10P2.regs0 Pab10P2.regs_out4 KS_ab10P2_4 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P2_5 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P2.regs0 Pab10P2.regs_out5).
Lemma KS_ab10P2_5_ok : BG.kept_ok 60 Pab10P2.regs0 Pab10P2.regs_out5 KS_ab10P2_5 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P2_6 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P2.regs0 Pab10P2.regs_out6).
Lemma KS_ab10P2_6_ok : BG.kept_ok 60 Pab10P2.regs0 Pab10P2.regs_out6 KS_ab10P2_6 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P2_7 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P2.regs0 Pab10P2.regs_out7).
Lemma KS_ab10P2_7_ok : BG.kept_ok 60 Pab10P2.regs0 Pab10P2.regs_out7 KS_ab10P2_7 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ab10P2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 16) -> getr R (reg 5) = Z_to_bv 64 13 -> getr R (reg 6) = Z_to_bv 64 2147450880 -> getr R (reg 7) = Z_to_bv 64 8185 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 (V 36%nat) -> getr R (reg 13) = Z_to_bv 64 (V 34%nat) -> getr R (reg 14) = Z_to_bv 64 5 -> getr R (reg 15) = Z_to_bv 64 10 -> getr R (reg 16) = Z_to_bv 64 2 -> getr R (reg 17) = Z_to_bv 64 1 -> getr R (reg 28) = Z_to_bv 64 146496 ->
  1 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 34%nat) <= 140737488355328 -> 0 <= (V 36%nat) <= 18446744073709551615 -> L5.u8_at RSEGS M (V 33%nat) (V 37%nat) ->
  0 <= (V 37%nat) <= 255 -> L5.u8_at RSEGS M (((V 33%nat) / 8) + 2147450880) 2 -> 0 <= Z.land (V 33%nat) 7 <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab1c M')
        /\ (forall x, In x KS_ab10P2_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 5
        /\ bv_unsigned (getr R' (reg 29)) = (Z.land (V 33%nat) 7)
        /\ (((V 37%nat) + 18446744073709551568) mod 2 ^ 64) < 10
        /\ (((V 36%nat) - 5) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab60 M')
        /\ (forall x, In x KS_ab10P2_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 37%nat) - 48)
        /\ bv_unsigned (getr R' (reg 29)) = (Z.land (V 33%nat) 7)
        /\ 10 <= (((V 37%nat) + 18446744073709551568) mod 2 ^ 64)
        /\ (((V 36%nat) - 5) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab1c M')
        /\ (forall x, In x KS_ab10P2_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 5
        /\ bv_unsigned (getr R' (reg 29)) = (Z.land (V 33%nat) 7)
        /\ (((V 37%nat) + 18446744073709551568) mod 2 ^ 64) < 10
        /\ (((V 36%nat) - 1) mod 2 ^ 64) < 1
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab60 M')
        /\ (forall x, In x KS_ab10P2_3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 37%nat) - 48)
        /\ bv_unsigned (getr R' (reg 29)) = (Z.land (V 33%nat) 7)
        /\ 10 <= (((V 37%nat) + 18446744073709551568) mod 2 ^ 64)
        /\ (((V 36%nat) - 1) mod 2 ^ 64) < 1
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab60 M')
        /\ (forall x, In x KS_ab10P2_4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ bv_unsigned (getr R' (reg 12)) = (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255)
        /\ bv_unsigned (getr R' (reg 29)) = (Z.land (8185 / 2 ^ ((((V 37%nat) + 18446744073709551571) mod 2 ^ 64) mod 64)) 1)
        /\ (((Z.land (8185 / 2 ^ ((((V 37%nat) + 18446744073709551571) mod 2 ^ 64) mod 64)) 1) - 0) mod 2 ^ 64) < 1
        /\ (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255) < 13
        /\ (((V 36%nat) - 0) mod 2 ^ 64) < 1
        /\ 1 <= (((V 36%nat) - 1) mod 2 ^ 64)
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbaab4 M')
        /\ (forall x, In x KS_ab10P2_5 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 12)) = ((((4 * (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255)) mod 2 ^ 64) + 146496) mod 2 ^ 64)
        /\ bv_unsigned (getr R' (reg 29)) = (Z.land (8185 / 2 ^ ((((V 37%nat) + 18446744073709551571) mod 2 ^ 64) mod 64)) 1)
        /\ 1 <= (((Z.land (8185 / 2 ^ ((((V 37%nat) + 18446744073709551571) mod 2 ^ 64) mod 64)) 1) - 0) mod 2 ^ 64)
        /\ (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255) < 13
        /\ (((V 36%nat) - 0) mod 2 ^ 64) < 1
        /\ 1 <= (((V 36%nat) - 1) mod 2 ^ 64)
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab60 M')
        /\ (forall x, In x KS_ab10P2_6 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ bv_unsigned (getr R' (reg 12)) = (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255)
        /\ getr R' (reg 29) = Z_to_bv 64 ((V 37%nat) - 45)
        /\ 13 <= (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255)
        /\ (((V 36%nat) - 0) mod 2 ^ 64) < 1
        /\ 1 <= (((V 36%nat) - 1) mod 2 ^ 64)
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab1c M')
        /\ (forall x, In x KS_ab10P2_7 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ 1 <= (((V 36%nat) - 0) mod 2 ^ 64)
        /\ 1 <= (((V 36%nat) - 1) mod 2 ^ 64)
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G5 G6 G7 G10 G11 G12 G13 G14 G15 G16 G17 G28 pvzI6 pvzI7 pvzI8 K3 pvzI9 K5 pvzI10.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K1l; move K1l before pvzI7; pose proof (proj2 pvzI7) as K1r; move K1r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K2l; move K2l before pvzI8; pose proof (proj2 pvzI8) as K2r; move K2r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K4l; move K4l before pvzI9; pose proof (proj2 pvzI9) as K4r; move K4r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E Pab10P2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pab10P2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pab10P2.kn0).
  { unfold know_ok, Pab10P2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K6l K6r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K1l K1r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K2l K2r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K6l K6r) | evalEk ZA ltac:(clear - HV37l HV37r K4l K4r) | clear - HV33l HV33r K0l K0r K6l K6r; lia | clear - HV33l HV33r K0l K0r K6l K6r; lia | byte_tac ltac:(clear - HV37l HV37r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K6l K6r; lia | clear - HV33l HV33r K0l K0r K6l K6r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K6l K6r) | clear; lia | exact (conj K6l K6r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pab10P2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pab10P2.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pab10P2.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc Pab10P2.ps0) with 0xbab1c in Hms. change (SR.ps_regs Pab10P2.ps0) with (map (fun i => (i, nth i Pab10P2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P2.ps0) with Pab10P2.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P2.regs0 Pab10P2.regs_out0 60 KS_ab10P2_0 KS_ab10P2_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pab10P2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P2.regs_out0 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P2.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. left.
    change (SR.ps_pc Pab10P2.ps1) with 0xbab60 in Hms. change (SR.ps_regs Pab10P2.ps1) with (map (fun i => (i, nth i Pab10P2.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P2.ps1) with Pab10P2.cells1 in Hcells. unfold Pab10P2.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P2.regs0 Pab10P2.regs_out1 60 KS_ab10P2_1 KS_ab10P2_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P2.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P2.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P2.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P2.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P2.regs_out1 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P2.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. left.
    change (SR.ps_pc Pab10P2.ps2) with 0xbab1c in Hms. change (SR.ps_regs Pab10P2.ps2) with (map (fun i => (i, nth i Pab10P2.regs_out2 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P2.ps2) with Pab10P2.cells2 in Hcells. unfold Pab10P2.cells2 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P2.regs0 Pab10P2.regs_out2 60 KS_ab10P2_2 KS_ab10P2_2_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P2.regs_out2 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P2.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P2.regs_out2 E' R' 11 Hregs) by (clear; lia). cbn [nth Pab10P2.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P2.regs_out2 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P2.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P2.regs_out2 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P2.regs_out2]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. left.
    change (SR.ps_pc Pab10P2.ps3) with 0xbab60 in Hms. change (SR.ps_regs Pab10P2.ps3) with (map (fun i => (i, nth i Pab10P2.regs_out3 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P2.ps3) with Pab10P2.cells3 in Hcells. unfold Pab10P2.cells3 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P2.regs0 Pab10P2.regs_out3 60 KS_ab10P2_3 KS_ab10P2_3_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P2.regs_out3 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P2.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P2.regs_out3 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P2.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P2.regs_out3 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P2.regs_out3]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. left.
    change (SR.ps_pc Pab10P2.ps4) with 0xbab60 in Hms. change (SR.ps_regs Pab10P2.ps4) with (map (fun i => (i, nth i Pab10P2.regs_out4 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P2.ps4) with Pab10P2.cells4 in Hcells. unfold Pab10P2.cells4 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P2.regs0 Pab10P2.regs_out4 60 KS_ab10P2_4 KS_ab10P2_4_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P2.regs_out4 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P2.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P2.regs_out4 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P2.regs_out4]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg Pab10P2.regs_out4 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P2.regs_out4]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. left.
    change (SR.ps_pc Pab10P2.ps5) with 0xbaab4 in Hms. change (SR.ps_regs Pab10P2.ps5) with (map (fun i => (i, nth i Pab10P2.regs_out5 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P2.ps5) with Pab10P2.cells5 in Hcells. unfold Pab10P2.cells5 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P2.regs0 Pab10P2.regs_out5 60 KS_ab10P2_5 KS_ab10P2_5_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P2.regs_out5 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P2.regs_out5]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg Pab10P2.regs_out5 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P2.regs_out5]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. left.
    change (SR.ps_pc Pab10P2.ps6) with 0xbab60 in Hms. change (SR.ps_regs Pab10P2.ps6) with (map (fun i => (i, nth i Pab10P2.regs_out6 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P2.ps6) with Pab10P2.cells6 in Hcells. unfold Pab10P2.cells6 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P2.regs0 Pab10P2.regs_out6 60 KS_ab10P2_6 KS_ab10P2_6_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P2.regs_out6 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P2.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P2.regs_out6 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P2.regs_out6]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg Pab10P2.regs_out6 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P2.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right.
    change (SR.ps_pc Pab10P2.ps7) with 0xbab1c in Hms. change (SR.ps_regs Pab10P2.ps7) with (map (fun i => (i, nth i Pab10P2.regs_out7 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P2.ps7) with Pab10P2.cells7 in Hcells. unfold Pab10P2.cells7 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P2.regs0 Pab10P2.regs_out7 60 KS_ab10P2_7 KS_ab10P2_7_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P2.regs_out7 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P2.regs_out7]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P2.regs_out7 E' R' 11 Hregs) by (clear; lia). cbn [nth Pab10P2.regs_out7]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.

Module Pab10P3 := BndP_Eb_000S9.LibSegEb_ab10P3.
Definition KS_ab10P3_0 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P3.regs0 Pab10P3.regs_out0).
Lemma KS_ab10P3_0_ok : BG.kept_ok 60 Pab10P3.regs0 Pab10P3.regs_out0 KS_ab10P3_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P3_1 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P3.regs0 Pab10P3.regs_out1).
Lemma KS_ab10P3_1_ok : BG.kept_ok 60 Pab10P3.regs0 Pab10P3.regs_out1 KS_ab10P3_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P3_2 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P3.regs0 Pab10P3.regs_out2).
Lemma KS_ab10P3_2_ok : BG.kept_ok 60 Pab10P3.regs0 Pab10P3.regs_out2 KS_ab10P3_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P3_3 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P3.regs0 Pab10P3.regs_out3).
Lemma KS_ab10P3_3_ok : BG.kept_ok 60 Pab10P3.regs0 Pab10P3.regs_out3 KS_ab10P3_3 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P3_4 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P3.regs0 Pab10P3.regs_out4).
Lemma KS_ab10P3_4_ok : BG.kept_ok 60 Pab10P3.regs0 Pab10P3.regs_out4 KS_ab10P3_4 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P3_5 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P3.regs0 Pab10P3.regs_out5).
Lemma KS_ab10P3_5_ok : BG.kept_ok 60 Pab10P3.regs0 Pab10P3.regs_out5 KS_ab10P3_5 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P3_6 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P3.regs0 Pab10P3.regs_out6).
Lemma KS_ab10P3_6_ok : BG.kept_ok 60 Pab10P3.regs0 Pab10P3.regs_out6 KS_ab10P3_6 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P3_7 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P3.regs0 Pab10P3.regs_out7).
Lemma KS_ab10P3_7_ok : BG.kept_ok 60 Pab10P3.regs0 Pab10P3.regs_out7 KS_ab10P3_7 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ab10P3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 16) -> getr R (reg 5) = Z_to_bv 64 13 -> getr R (reg 6) = Z_to_bv 64 2147450880 -> getr R (reg 7) = Z_to_bv 64 8185 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 (V 36%nat) -> getr R (reg 13) = Z_to_bv 64 (V 34%nat) -> getr R (reg 14) = Z_to_bv 64 5 -> getr R (reg 15) = Z_to_bv 64 10 -> getr R (reg 16) = Z_to_bv 64 2 -> getr R (reg 17) = Z_to_bv 64 1 -> getr R (reg 28) = Z_to_bv 64 146496 ->
  1 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 34%nat) <= 140737488355328 -> 0 <= (V 36%nat) <= 18446744073709551615 -> L5.u8_at RSEGS M (V 33%nat) (V 37%nat) ->
  0 <= (V 37%nat) <= 255 -> L5.u8_at RSEGS M (((V 33%nat) / 8) + 2147450880) 3 -> 0 <= Z.land (V 33%nat) 7 <= 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab1c M')
        /\ (forall x, In x KS_ab10P3_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 5
        /\ bv_unsigned (getr R' (reg 29)) = (Z.land (V 33%nat) 7)
        /\ (((V 37%nat) + 18446744073709551568) mod 2 ^ 64) < 10
        /\ (((V 36%nat) - 5) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab60 M')
        /\ (forall x, In x KS_ab10P3_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 37%nat) - 48)
        /\ bv_unsigned (getr R' (reg 29)) = (Z.land (V 33%nat) 7)
        /\ 10 <= (((V 37%nat) + 18446744073709551568) mod 2 ^ 64)
        /\ (((V 36%nat) - 5) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab1c M')
        /\ (forall x, In x KS_ab10P3_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 5
        /\ bv_unsigned (getr R' (reg 29)) = (Z.land (V 33%nat) 7)
        /\ (((V 37%nat) + 18446744073709551568) mod 2 ^ 64) < 10
        /\ (((V 36%nat) - 1) mod 2 ^ 64) < 1
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab60 M')
        /\ (forall x, In x KS_ab10P3_3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 37%nat) - 48)
        /\ bv_unsigned (getr R' (reg 29)) = (Z.land (V 33%nat) 7)
        /\ 10 <= (((V 37%nat) + 18446744073709551568) mod 2 ^ 64)
        /\ (((V 36%nat) - 1) mod 2 ^ 64) < 1
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab60 M')
        /\ (forall x, In x KS_ab10P3_4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ bv_unsigned (getr R' (reg 12)) = (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255)
        /\ bv_unsigned (getr R' (reg 29)) = (Z.land (8185 / 2 ^ ((((V 37%nat) + 18446744073709551571) mod 2 ^ 64) mod 64)) 1)
        /\ (((Z.land (8185 / 2 ^ ((((V 37%nat) + 18446744073709551571) mod 2 ^ 64) mod 64)) 1) - 0) mod 2 ^ 64) < 1
        /\ (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255) < 13
        /\ (((V 36%nat) - 0) mod 2 ^ 64) < 1
        /\ 1 <= (((V 36%nat) - 1) mod 2 ^ 64)
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbaab4 M')
        /\ (forall x, In x KS_ab10P3_5 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 12)) = ((((4 * (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255)) mod 2 ^ 64) + 146496) mod 2 ^ 64)
        /\ bv_unsigned (getr R' (reg 29)) = (Z.land (8185 / 2 ^ ((((V 37%nat) + 18446744073709551571) mod 2 ^ 64) mod 64)) 1)
        /\ 1 <= (((Z.land (8185 / 2 ^ ((((V 37%nat) + 18446744073709551571) mod 2 ^ 64) mod 64)) 1) - 0) mod 2 ^ 64)
        /\ (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255) < 13
        /\ (((V 36%nat) - 0) mod 2 ^ 64) < 1
        /\ 1 <= (((V 36%nat) - 1) mod 2 ^ 64)
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab60 M')
        /\ (forall x, In x KS_ab10P3_6 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ bv_unsigned (getr R' (reg 12)) = (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255)
        /\ getr R' (reg 29) = Z_to_bv 64 ((V 37%nat) - 45)
        /\ 13 <= (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255)
        /\ (((V 36%nat) - 0) mod 2 ^ 64) < 1
        /\ 1 <= (((V 36%nat) - 1) mod 2 ^ 64)
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab1c M')
        /\ (forall x, In x KS_ab10P3_7 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ 1 <= (((V 36%nat) - 0) mod 2 ^ 64)
        /\ 1 <= (((V 36%nat) - 1) mod 2 ^ 64)
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G5 G6 G7 G10 G11 G12 G13 G14 G15 G16 G17 G28 pvzI6 pvzI7 pvzI8 K3 pvzI9 K5 pvzI10.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K1l; move K1l before pvzI7; pose proof (proj2 pvzI7) as K1r; move K1r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K2l; move K2l before pvzI8; pose proof (proj2 pvzI8) as K2r; move K2r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K4l; move K4l before pvzI9; pose proof (proj2 pvzI9) as K4r; move K4r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E Pab10P3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pab10P3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pab10P3.kn0).
  { unfold know_ok, Pab10P3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K6l K6r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K1l K1r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K2l K2r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K6l K6r) | evalEk ZA ltac:(clear - HV37l HV37r K4l K4r) | clear - HV33l HV33r K0l K0r K6l K6r; lia | clear - HV33l HV33r K0l K0r K6l K6r; lia | byte_tac ltac:(clear - HV37l HV37r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K6l K6r; lia | clear - HV33l HV33r K0l K0r K6l K6r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K6l K6r) | clear; lia | exact (conj K6l K6r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pab10P3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pab10P3.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pab10P3.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc Pab10P3.ps0) with 0xbab1c in Hms. change (SR.ps_regs Pab10P3.ps0) with (map (fun i => (i, nth i Pab10P3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P3.ps0) with Pab10P3.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P3.regs0 Pab10P3.regs_out0 60 KS_ab10P3_0 KS_ab10P3_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pab10P3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P3.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P3.regs_out0 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P3.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. left.
    change (SR.ps_pc Pab10P3.ps1) with 0xbab60 in Hms. change (SR.ps_regs Pab10P3.ps1) with (map (fun i => (i, nth i Pab10P3.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P3.ps1) with Pab10P3.cells1 in Hcells. unfold Pab10P3.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P3.regs0 Pab10P3.regs_out1 60 KS_ab10P3_1 KS_ab10P3_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P3.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P3.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P3.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P3.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P3.regs_out1 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P3.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. left.
    change (SR.ps_pc Pab10P3.ps2) with 0xbab1c in Hms. change (SR.ps_regs Pab10P3.ps2) with (map (fun i => (i, nth i Pab10P3.regs_out2 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P3.ps2) with Pab10P3.cells2 in Hcells. unfold Pab10P3.cells2 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P3.regs0 Pab10P3.regs_out2 60 KS_ab10P3_2 KS_ab10P3_2_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P3.regs_out2 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P3.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P3.regs_out2 E' R' 11 Hregs) by (clear; lia). cbn [nth Pab10P3.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P3.regs_out2 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P3.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P3.regs_out2 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P3.regs_out2]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. left.
    change (SR.ps_pc Pab10P3.ps3) with 0xbab60 in Hms. change (SR.ps_regs Pab10P3.ps3) with (map (fun i => (i, nth i Pab10P3.regs_out3 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P3.ps3) with Pab10P3.cells3 in Hcells. unfold Pab10P3.cells3 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P3.regs0 Pab10P3.regs_out3 60 KS_ab10P3_3 KS_ab10P3_3_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P3.regs_out3 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P3.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P3.regs_out3 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P3.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P3.regs_out3 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P3.regs_out3]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. left.
    change (SR.ps_pc Pab10P3.ps4) with 0xbab60 in Hms. change (SR.ps_regs Pab10P3.ps4) with (map (fun i => (i, nth i Pab10P3.regs_out4 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P3.ps4) with Pab10P3.cells4 in Hcells. unfold Pab10P3.cells4 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P3.regs0 Pab10P3.regs_out4 60 KS_ab10P3_4 KS_ab10P3_4_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P3.regs_out4 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P3.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P3.regs_out4 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P3.regs_out4]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg Pab10P3.regs_out4 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P3.regs_out4]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. left.
    change (SR.ps_pc Pab10P3.ps5) with 0xbaab4 in Hms. change (SR.ps_regs Pab10P3.ps5) with (map (fun i => (i, nth i Pab10P3.regs_out5 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P3.ps5) with Pab10P3.cells5 in Hcells. unfold Pab10P3.cells5 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P3.regs0 Pab10P3.regs_out5 60 KS_ab10P3_5 KS_ab10P3_5_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P3.regs_out5 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P3.regs_out5]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg Pab10P3.regs_out5 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P3.regs_out5]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. left.
    change (SR.ps_pc Pab10P3.ps6) with 0xbab60 in Hms. change (SR.ps_regs Pab10P3.ps6) with (map (fun i => (i, nth i Pab10P3.regs_out6 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P3.ps6) with Pab10P3.cells6 in Hcells. unfold Pab10P3.cells6 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P3.regs0 Pab10P3.regs_out6 60 KS_ab10P3_6 KS_ab10P3_6_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P3.regs_out6 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P3.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P3.regs_out6 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P3.regs_out6]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg Pab10P3.regs_out6 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P3.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right.
    change (SR.ps_pc Pab10P3.ps7) with 0xbab1c in Hms. change (SR.ps_regs Pab10P3.ps7) with (map (fun i => (i, nth i Pab10P3.regs_out7 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P3.ps7) with Pab10P3.cells7 in Hcells. unfold Pab10P3.cells7 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P3.regs0 Pab10P3.regs_out7 60 KS_ab10P3_7 KS_ab10P3_7_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P3.regs_out7 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P3.regs_out7]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P3.regs_out7 E' R' 11 Hregs) by (clear; lia). cbn [nth Pab10P3.regs_out7]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.

Module Pab10P4 := BndP_Eb_000S9.LibSegEb_ab10P4.
Definition KS_ab10P4_0 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P4.regs0 Pab10P4.regs_out0).
Lemma KS_ab10P4_0_ok : BG.kept_ok 60 Pab10P4.regs0 Pab10P4.regs_out0 KS_ab10P4_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P4_1 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P4.regs0 Pab10P4.regs_out1).
Lemma KS_ab10P4_1_ok : BG.kept_ok 60 Pab10P4.regs0 Pab10P4.regs_out1 KS_ab10P4_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P4_2 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P4.regs0 Pab10P4.regs_out2).
Lemma KS_ab10P4_2_ok : BG.kept_ok 60 Pab10P4.regs0 Pab10P4.regs_out2 KS_ab10P4_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P4_3 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P4.regs0 Pab10P4.regs_out3).
Lemma KS_ab10P4_3_ok : BG.kept_ok 60 Pab10P4.regs0 Pab10P4.regs_out3 KS_ab10P4_3 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P4_4 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P4.regs0 Pab10P4.regs_out4).
Lemma KS_ab10P4_4_ok : BG.kept_ok 60 Pab10P4.regs0 Pab10P4.regs_out4 KS_ab10P4_4 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P4_5 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P4.regs0 Pab10P4.regs_out5).
Lemma KS_ab10P4_5_ok : BG.kept_ok 60 Pab10P4.regs0 Pab10P4.regs_out5 KS_ab10P4_5 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P4_6 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P4.regs0 Pab10P4.regs_out6).
Lemma KS_ab10P4_6_ok : BG.kept_ok 60 Pab10P4.regs0 Pab10P4.regs_out6 KS_ab10P4_6 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P4_7 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P4.regs0 Pab10P4.regs_out7).
Lemma KS_ab10P4_7_ok : BG.kept_ok 60 Pab10P4.regs0 Pab10P4.regs_out7 KS_ab10P4_7 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ab10P4_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 16) -> getr R (reg 5) = Z_to_bv 64 13 -> getr R (reg 6) = Z_to_bv 64 2147450880 -> getr R (reg 7) = Z_to_bv 64 8185 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 (V 36%nat) -> getr R (reg 13) = Z_to_bv 64 (V 34%nat) -> getr R (reg 14) = Z_to_bv 64 5 -> getr R (reg 15) = Z_to_bv 64 10 -> getr R (reg 16) = Z_to_bv 64 2 -> getr R (reg 17) = Z_to_bv 64 1 -> getr R (reg 28) = Z_to_bv 64 146496 ->
  1 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 34%nat) <= 140737488355328 -> 0 <= (V 36%nat) <= 18446744073709551615 -> L5.u8_at RSEGS M (V 33%nat) (V 37%nat) ->
  0 <= (V 37%nat) <= 255 -> L5.u8_at RSEGS M (((V 33%nat) / 8) + 2147450880) 4 -> 0 <= Z.land (V 33%nat) 7 <= 3 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab1c M')
        /\ (forall x, In x KS_ab10P4_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 5
        /\ bv_unsigned (getr R' (reg 29)) = (Z.land (V 33%nat) 7)
        /\ (((V 37%nat) + 18446744073709551568) mod 2 ^ 64) < 10
        /\ (((V 36%nat) - 5) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab60 M')
        /\ (forall x, In x KS_ab10P4_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 37%nat) - 48)
        /\ bv_unsigned (getr R' (reg 29)) = (Z.land (V 33%nat) 7)
        /\ 10 <= (((V 37%nat) + 18446744073709551568) mod 2 ^ 64)
        /\ (((V 36%nat) - 5) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab1c M')
        /\ (forall x, In x KS_ab10P4_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 5
        /\ bv_unsigned (getr R' (reg 29)) = (Z.land (V 33%nat) 7)
        /\ (((V 37%nat) + 18446744073709551568) mod 2 ^ 64) < 10
        /\ (((V 36%nat) - 1) mod 2 ^ 64) < 1
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab60 M')
        /\ (forall x, In x KS_ab10P4_3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 37%nat) - 48)
        /\ bv_unsigned (getr R' (reg 29)) = (Z.land (V 33%nat) 7)
        /\ 10 <= (((V 37%nat) + 18446744073709551568) mod 2 ^ 64)
        /\ (((V 36%nat) - 1) mod 2 ^ 64) < 1
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab60 M')
        /\ (forall x, In x KS_ab10P4_4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ bv_unsigned (getr R' (reg 12)) = (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255)
        /\ bv_unsigned (getr R' (reg 29)) = (Z.land (8185 / 2 ^ ((((V 37%nat) + 18446744073709551571) mod 2 ^ 64) mod 64)) 1)
        /\ (((Z.land (8185 / 2 ^ ((((V 37%nat) + 18446744073709551571) mod 2 ^ 64) mod 64)) 1) - 0) mod 2 ^ 64) < 1
        /\ (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255) < 13
        /\ (((V 36%nat) - 0) mod 2 ^ 64) < 1
        /\ 1 <= (((V 36%nat) - 1) mod 2 ^ 64)
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbaab4 M')
        /\ (forall x, In x KS_ab10P4_5 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 12)) = ((((4 * (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255)) mod 2 ^ 64) + 146496) mod 2 ^ 64)
        /\ bv_unsigned (getr R' (reg 29)) = (Z.land (8185 / 2 ^ ((((V 37%nat) + 18446744073709551571) mod 2 ^ 64) mod 64)) 1)
        /\ 1 <= (((Z.land (8185 / 2 ^ ((((V 37%nat) + 18446744073709551571) mod 2 ^ 64) mod 64)) 1) - 0) mod 2 ^ 64)
        /\ (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255) < 13
        /\ (((V 36%nat) - 0) mod 2 ^ 64) < 1
        /\ 1 <= (((V 36%nat) - 1) mod 2 ^ 64)
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab60 M')
        /\ (forall x, In x KS_ab10P4_6 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ bv_unsigned (getr R' (reg 12)) = (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255)
        /\ getr R' (reg 29) = Z_to_bv 64 ((V 37%nat) - 45)
        /\ 13 <= (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255)
        /\ (((V 36%nat) - 0) mod 2 ^ 64) < 1
        /\ 1 <= (((V 36%nat) - 1) mod 2 ^ 64)
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab1c M')
        /\ (forall x, In x KS_ab10P4_7 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ 1 <= (((V 36%nat) - 0) mod 2 ^ 64)
        /\ 1 <= (((V 36%nat) - 1) mod 2 ^ 64)
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G5 G6 G7 G10 G11 G12 G13 G14 G15 G16 G17 G28 pvzI6 pvzI7 pvzI8 K3 pvzI9 K5 pvzI10.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K1l; move K1l before pvzI7; pose proof (proj2 pvzI7) as K1r; move K1r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K2l; move K2l before pvzI8; pose proof (proj2 pvzI8) as K2r; move K2r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K4l; move K4l before pvzI9; pose proof (proj2 pvzI9) as K4r; move K4r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E Pab10P4.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pab10P4.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pab10P4.kn0).
  { unfold know_ok, Pab10P4.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K6l K6r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K1l K1r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K2l K2r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K6l K6r) | evalEk ZA ltac:(clear - HV37l HV37r K4l K4r) | clear - HV33l HV33r K0l K0r K6l K6r; lia | clear - HV33l HV33r K0l K0r K6l K6r; lia | byte_tac ltac:(clear - HV37l HV37r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K6l K6r; lia | clear - HV33l HV33r K0l K0r K6l K6r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K6l K6r) | clear; lia | exact (conj K6l K6r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pab10P4.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pab10P4.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pab10P4.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc Pab10P4.ps0) with 0xbab1c in Hms. change (SR.ps_regs Pab10P4.ps0) with (map (fun i => (i, nth i Pab10P4.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P4.ps0) with Pab10P4.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P4.regs0 Pab10P4.regs_out0 60 KS_ab10P4_0 KS_ab10P4_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P4.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P4.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pab10P4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P4.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P4.regs_out0 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P4.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. left.
    change (SR.ps_pc Pab10P4.ps1) with 0xbab60 in Hms. change (SR.ps_regs Pab10P4.ps1) with (map (fun i => (i, nth i Pab10P4.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P4.ps1) with Pab10P4.cells1 in Hcells. unfold Pab10P4.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P4.regs0 Pab10P4.regs_out1 60 KS_ab10P4_1 KS_ab10P4_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P4.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P4.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P4.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P4.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P4.regs_out1 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P4.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. left.
    change (SR.ps_pc Pab10P4.ps2) with 0xbab1c in Hms. change (SR.ps_regs Pab10P4.ps2) with (map (fun i => (i, nth i Pab10P4.regs_out2 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P4.ps2) with Pab10P4.cells2 in Hcells. unfold Pab10P4.cells2 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P4.regs0 Pab10P4.regs_out2 60 KS_ab10P4_2 KS_ab10P4_2_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P4.regs_out2 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P4.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P4.regs_out2 E' R' 11 Hregs) by (clear; lia). cbn [nth Pab10P4.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P4.regs_out2 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P4.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P4.regs_out2 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P4.regs_out2]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. left.
    change (SR.ps_pc Pab10P4.ps3) with 0xbab60 in Hms. change (SR.ps_regs Pab10P4.ps3) with (map (fun i => (i, nth i Pab10P4.regs_out3 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P4.ps3) with Pab10P4.cells3 in Hcells. unfold Pab10P4.cells3 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P4.regs0 Pab10P4.regs_out3 60 KS_ab10P4_3 KS_ab10P4_3_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P4.regs_out3 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P4.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P4.regs_out3 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P4.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P4.regs_out3 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P4.regs_out3]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. left.
    change (SR.ps_pc Pab10P4.ps4) with 0xbab60 in Hms. change (SR.ps_regs Pab10P4.ps4) with (map (fun i => (i, nth i Pab10P4.regs_out4 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P4.ps4) with Pab10P4.cells4 in Hcells. unfold Pab10P4.cells4 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P4.regs0 Pab10P4.regs_out4 60 KS_ab10P4_4 KS_ab10P4_4_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P4.regs_out4 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P4.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P4.regs_out4 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P4.regs_out4]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg Pab10P4.regs_out4 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P4.regs_out4]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. left.
    change (SR.ps_pc Pab10P4.ps5) with 0xbaab4 in Hms. change (SR.ps_regs Pab10P4.ps5) with (map (fun i => (i, nth i Pab10P4.regs_out5 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P4.ps5) with Pab10P4.cells5 in Hcells. unfold Pab10P4.cells5 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P4.regs0 Pab10P4.regs_out5 60 KS_ab10P4_5 KS_ab10P4_5_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P4.regs_out5 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P4.regs_out5]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg Pab10P4.regs_out5 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P4.regs_out5]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. left.
    change (SR.ps_pc Pab10P4.ps6) with 0xbab60 in Hms. change (SR.ps_regs Pab10P4.ps6) with (map (fun i => (i, nth i Pab10P4.regs_out6 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P4.ps6) with Pab10P4.cells6 in Hcells. unfold Pab10P4.cells6 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P4.regs0 Pab10P4.regs_out6 60 KS_ab10P4_6 KS_ab10P4_6_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P4.regs_out6 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P4.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P4.regs_out6 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P4.regs_out6]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg Pab10P4.regs_out6 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P4.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right.
    change (SR.ps_pc Pab10P4.ps7) with 0xbab1c in Hms. change (SR.ps_regs Pab10P4.ps7) with (map (fun i => (i, nth i Pab10P4.regs_out7 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P4.ps7) with Pab10P4.cells7 in Hcells. unfold Pab10P4.cells7 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P4.regs0 Pab10P4.regs_out7 60 KS_ab10P4_7 KS_ab10P4_7_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P4.regs_out7 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P4.regs_out7]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P4.regs_out7 E' R' 11 Hregs) by (clear; lia). cbn [nth Pab10P4.regs_out7]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.

Module Pab10P5 := BndP_Eb_000S9.LibSegEb_ab10P5.
Definition KS_ab10P5_0 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P5.regs0 Pab10P5.regs_out0).
Lemma KS_ab10P5_0_ok : BG.kept_ok 60 Pab10P5.regs0 Pab10P5.regs_out0 KS_ab10P5_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P5_1 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P5.regs0 Pab10P5.regs_out1).
Lemma KS_ab10P5_1_ok : BG.kept_ok 60 Pab10P5.regs0 Pab10P5.regs_out1 KS_ab10P5_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P5_2 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P5.regs0 Pab10P5.regs_out2).
Lemma KS_ab10P5_2_ok : BG.kept_ok 60 Pab10P5.regs0 Pab10P5.regs_out2 KS_ab10P5_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P5_3 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P5.regs0 Pab10P5.regs_out3).
Lemma KS_ab10P5_3_ok : BG.kept_ok 60 Pab10P5.regs0 Pab10P5.regs_out3 KS_ab10P5_3 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P5_4 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P5.regs0 Pab10P5.regs_out4).
Lemma KS_ab10P5_4_ok : BG.kept_ok 60 Pab10P5.regs0 Pab10P5.regs_out4 KS_ab10P5_4 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P5_5 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P5.regs0 Pab10P5.regs_out5).
Lemma KS_ab10P5_5_ok : BG.kept_ok 60 Pab10P5.regs0 Pab10P5.regs_out5 KS_ab10P5_5 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P5_6 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P5.regs0 Pab10P5.regs_out6).
Lemma KS_ab10P5_6_ok : BG.kept_ok 60 Pab10P5.regs0 Pab10P5.regs_out6 KS_ab10P5_6 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P5_7 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P5.regs0 Pab10P5.regs_out7).
Lemma KS_ab10P5_7_ok : BG.kept_ok 60 Pab10P5.regs0 Pab10P5.regs_out7 KS_ab10P5_7 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ab10P5_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 16) -> getr R (reg 5) = Z_to_bv 64 13 -> getr R (reg 6) = Z_to_bv 64 2147450880 -> getr R (reg 7) = Z_to_bv 64 8185 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 (V 36%nat) -> getr R (reg 13) = Z_to_bv 64 (V 34%nat) -> getr R (reg 14) = Z_to_bv 64 5 -> getr R (reg 15) = Z_to_bv 64 10 -> getr R (reg 16) = Z_to_bv 64 2 -> getr R (reg 17) = Z_to_bv 64 1 -> getr R (reg 28) = Z_to_bv 64 146496 ->
  1 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 34%nat) <= 140737488355328 -> 0 <= (V 36%nat) <= 18446744073709551615 -> L5.u8_at RSEGS M (V 33%nat) (V 37%nat) ->
  0 <= (V 37%nat) <= 255 -> L5.u8_at RSEGS M (((V 33%nat) / 8) + 2147450880) 5 -> 0 <= Z.land (V 33%nat) 7 <= 4 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab1c M')
        /\ (forall x, In x KS_ab10P5_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 5
        /\ bv_unsigned (getr R' (reg 29)) = (Z.land (V 33%nat) 7)
        /\ (((V 37%nat) + 18446744073709551568) mod 2 ^ 64) < 10
        /\ (((V 36%nat) - 5) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab60 M')
        /\ (forall x, In x KS_ab10P5_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 37%nat) - 48)
        /\ bv_unsigned (getr R' (reg 29)) = (Z.land (V 33%nat) 7)
        /\ 10 <= (((V 37%nat) + 18446744073709551568) mod 2 ^ 64)
        /\ (((V 36%nat) - 5) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab1c M')
        /\ (forall x, In x KS_ab10P5_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 5
        /\ bv_unsigned (getr R' (reg 29)) = (Z.land (V 33%nat) 7)
        /\ (((V 37%nat) + 18446744073709551568) mod 2 ^ 64) < 10
        /\ (((V 36%nat) - 1) mod 2 ^ 64) < 1
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab60 M')
        /\ (forall x, In x KS_ab10P5_3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 37%nat) - 48)
        /\ bv_unsigned (getr R' (reg 29)) = (Z.land (V 33%nat) 7)
        /\ 10 <= (((V 37%nat) + 18446744073709551568) mod 2 ^ 64)
        /\ (((V 36%nat) - 1) mod 2 ^ 64) < 1
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab60 M')
        /\ (forall x, In x KS_ab10P5_4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ bv_unsigned (getr R' (reg 12)) = (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255)
        /\ bv_unsigned (getr R' (reg 29)) = (Z.land (8185 / 2 ^ ((((V 37%nat) + 18446744073709551571) mod 2 ^ 64) mod 64)) 1)
        /\ (((Z.land (8185 / 2 ^ ((((V 37%nat) + 18446744073709551571) mod 2 ^ 64) mod 64)) 1) - 0) mod 2 ^ 64) < 1
        /\ (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255) < 13
        /\ (((V 36%nat) - 0) mod 2 ^ 64) < 1
        /\ 1 <= (((V 36%nat) - 1) mod 2 ^ 64)
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbaab4 M')
        /\ (forall x, In x KS_ab10P5_5 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 12)) = ((((4 * (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255)) mod 2 ^ 64) + 146496) mod 2 ^ 64)
        /\ bv_unsigned (getr R' (reg 29)) = (Z.land (8185 / 2 ^ ((((V 37%nat) + 18446744073709551571) mod 2 ^ 64) mod 64)) 1)
        /\ 1 <= (((Z.land (8185 / 2 ^ ((((V 37%nat) + 18446744073709551571) mod 2 ^ 64) mod 64)) 1) - 0) mod 2 ^ 64)
        /\ (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255) < 13
        /\ (((V 36%nat) - 0) mod 2 ^ 64) < 1
        /\ 1 <= (((V 36%nat) - 1) mod 2 ^ 64)
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab60 M')
        /\ (forall x, In x KS_ab10P5_6 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ bv_unsigned (getr R' (reg 12)) = (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255)
        /\ getr R' (reg 29) = Z_to_bv 64 ((V 37%nat) - 45)
        /\ 13 <= (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255)
        /\ (((V 36%nat) - 0) mod 2 ^ 64) < 1
        /\ 1 <= (((V 36%nat) - 1) mod 2 ^ 64)
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab1c M')
        /\ (forall x, In x KS_ab10P5_7 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ 1 <= (((V 36%nat) - 0) mod 2 ^ 64)
        /\ 1 <= (((V 36%nat) - 1) mod 2 ^ 64)
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G5 G6 G7 G10 G11 G12 G13 G14 G15 G16 G17 G28 pvzI6 pvzI7 pvzI8 K3 pvzI9 K5 pvzI10.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K1l; move K1l before pvzI7; pose proof (proj2 pvzI7) as K1r; move K1r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K2l; move K2l before pvzI8; pose proof (proj2 pvzI8) as K2r; move K2r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K4l; move K4l before pvzI9; pose proof (proj2 pvzI9) as K4r; move K4r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E Pab10P5.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pab10P5.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pab10P5.kn0).
  { unfold know_ok, Pab10P5.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K6l K6r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K1l K1r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K2l K2r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K6l K6r) | evalEk ZA ltac:(clear - HV37l HV37r K4l K4r) | clear - HV33l HV33r K0l K0r K6l K6r; lia | clear - HV33l HV33r K0l K0r K6l K6r; lia | byte_tac ltac:(clear - HV37l HV37r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K6l K6r; lia | clear - HV33l HV33r K0l K0r K6l K6r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K6l K6r) | clear; lia | exact (conj K6l K6r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pab10P5.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pab10P5.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pab10P5.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc Pab10P5.ps0) with 0xbab1c in Hms. change (SR.ps_regs Pab10P5.ps0) with (map (fun i => (i, nth i Pab10P5.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P5.ps0) with Pab10P5.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P5.regs0 Pab10P5.regs_out0 60 KS_ab10P5_0 KS_ab10P5_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P5.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P5.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pab10P5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P5.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P5.regs_out0 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P5.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. left.
    change (SR.ps_pc Pab10P5.ps1) with 0xbab60 in Hms. change (SR.ps_regs Pab10P5.ps1) with (map (fun i => (i, nth i Pab10P5.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P5.ps1) with Pab10P5.cells1 in Hcells. unfold Pab10P5.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P5.regs0 Pab10P5.regs_out1 60 KS_ab10P5_1 KS_ab10P5_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P5.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P5.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P5.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P5.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P5.regs_out1 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P5.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. left.
    change (SR.ps_pc Pab10P5.ps2) with 0xbab1c in Hms. change (SR.ps_regs Pab10P5.ps2) with (map (fun i => (i, nth i Pab10P5.regs_out2 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P5.ps2) with Pab10P5.cells2 in Hcells. unfold Pab10P5.cells2 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P5.regs0 Pab10P5.regs_out2 60 KS_ab10P5_2 KS_ab10P5_2_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P5.regs_out2 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P5.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P5.regs_out2 E' R' 11 Hregs) by (clear; lia). cbn [nth Pab10P5.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P5.regs_out2 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P5.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P5.regs_out2 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P5.regs_out2]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. left.
    change (SR.ps_pc Pab10P5.ps3) with 0xbab60 in Hms. change (SR.ps_regs Pab10P5.ps3) with (map (fun i => (i, nth i Pab10P5.regs_out3 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P5.ps3) with Pab10P5.cells3 in Hcells. unfold Pab10P5.cells3 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P5.regs0 Pab10P5.regs_out3 60 KS_ab10P5_3 KS_ab10P5_3_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P5.regs_out3 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P5.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P5.regs_out3 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P5.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P5.regs_out3 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P5.regs_out3]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. left.
    change (SR.ps_pc Pab10P5.ps4) with 0xbab60 in Hms. change (SR.ps_regs Pab10P5.ps4) with (map (fun i => (i, nth i Pab10P5.regs_out4 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P5.ps4) with Pab10P5.cells4 in Hcells. unfold Pab10P5.cells4 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P5.regs0 Pab10P5.regs_out4 60 KS_ab10P5_4 KS_ab10P5_4_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P5.regs_out4 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P5.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P5.regs_out4 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P5.regs_out4]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg Pab10P5.regs_out4 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P5.regs_out4]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. left.
    change (SR.ps_pc Pab10P5.ps5) with 0xbaab4 in Hms. change (SR.ps_regs Pab10P5.ps5) with (map (fun i => (i, nth i Pab10P5.regs_out5 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P5.ps5) with Pab10P5.cells5 in Hcells. unfold Pab10P5.cells5 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P5.regs0 Pab10P5.regs_out5 60 KS_ab10P5_5 KS_ab10P5_5_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P5.regs_out5 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P5.regs_out5]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg Pab10P5.regs_out5 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P5.regs_out5]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. left.
    change (SR.ps_pc Pab10P5.ps6) with 0xbab60 in Hms. change (SR.ps_regs Pab10P5.ps6) with (map (fun i => (i, nth i Pab10P5.regs_out6 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P5.ps6) with Pab10P5.cells6 in Hcells. unfold Pab10P5.cells6 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P5.regs0 Pab10P5.regs_out6 60 KS_ab10P5_6 KS_ab10P5_6_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P5.regs_out6 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P5.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P5.regs_out6 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P5.regs_out6]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg Pab10P5.regs_out6 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P5.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right.
    change (SR.ps_pc Pab10P5.ps7) with 0xbab1c in Hms. change (SR.ps_regs Pab10P5.ps7) with (map (fun i => (i, nth i Pab10P5.regs_out7 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P5.ps7) with Pab10P5.cells7 in Hcells. unfold Pab10P5.cells7 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P5.regs0 Pab10P5.regs_out7 60 KS_ab10P5_7 KS_ab10P5_7_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P5.regs_out7 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P5.regs_out7]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P5.regs_out7 E' R' 11 Hregs) by (clear; lia). cbn [nth Pab10P5.regs_out7]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.

Module Pab10P6 := BndP_Eb_000S9.LibSegEb_ab10P6.
Definition KS_ab10P6_0 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P6.regs0 Pab10P6.regs_out0).
Lemma KS_ab10P6_0_ok : BG.kept_ok 60 Pab10P6.regs0 Pab10P6.regs_out0 KS_ab10P6_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P6_1 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P6.regs0 Pab10P6.regs_out1).
Lemma KS_ab10P6_1_ok : BG.kept_ok 60 Pab10P6.regs0 Pab10P6.regs_out1 KS_ab10P6_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P6_2 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P6.regs0 Pab10P6.regs_out2).
Lemma KS_ab10P6_2_ok : BG.kept_ok 60 Pab10P6.regs0 Pab10P6.regs_out2 KS_ab10P6_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P6_3 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P6.regs0 Pab10P6.regs_out3).
Lemma KS_ab10P6_3_ok : BG.kept_ok 60 Pab10P6.regs0 Pab10P6.regs_out3 KS_ab10P6_3 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P6_4 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P6.regs0 Pab10P6.regs_out4).
Lemma KS_ab10P6_4_ok : BG.kept_ok 60 Pab10P6.regs0 Pab10P6.regs_out4 KS_ab10P6_4 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P6_5 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P6.regs0 Pab10P6.regs_out5).
Lemma KS_ab10P6_5_ok : BG.kept_ok 60 Pab10P6.regs0 Pab10P6.regs_out5 KS_ab10P6_5 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P6_6 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P6.regs0 Pab10P6.regs_out6).
Lemma KS_ab10P6_6_ok : BG.kept_ok 60 Pab10P6.regs0 Pab10P6.regs_out6 KS_ab10P6_6 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P6_7 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P6.regs0 Pab10P6.regs_out7).
Lemma KS_ab10P6_7_ok : BG.kept_ok 60 Pab10P6.regs0 Pab10P6.regs_out7 KS_ab10P6_7 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ab10P6_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 16) -> getr R (reg 5) = Z_to_bv 64 13 -> getr R (reg 6) = Z_to_bv 64 2147450880 -> getr R (reg 7) = Z_to_bv 64 8185 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 (V 36%nat) -> getr R (reg 13) = Z_to_bv 64 (V 34%nat) -> getr R (reg 14) = Z_to_bv 64 5 -> getr R (reg 15) = Z_to_bv 64 10 -> getr R (reg 16) = Z_to_bv 64 2 -> getr R (reg 17) = Z_to_bv 64 1 -> getr R (reg 28) = Z_to_bv 64 146496 ->
  1 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 34%nat) <= 140737488355328 -> 0 <= (V 36%nat) <= 18446744073709551615 -> L5.u8_at RSEGS M (V 33%nat) (V 37%nat) ->
  0 <= (V 37%nat) <= 255 -> L5.u8_at RSEGS M (((V 33%nat) / 8) + 2147450880) 6 -> 0 <= Z.land (V 33%nat) 7 <= 5 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab1c M')
        /\ (forall x, In x KS_ab10P6_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 5
        /\ bv_unsigned (getr R' (reg 29)) = (Z.land (V 33%nat) 7)
        /\ (((V 37%nat) + 18446744073709551568) mod 2 ^ 64) < 10
        /\ (((V 36%nat) - 5) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab60 M')
        /\ (forall x, In x KS_ab10P6_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 37%nat) - 48)
        /\ bv_unsigned (getr R' (reg 29)) = (Z.land (V 33%nat) 7)
        /\ 10 <= (((V 37%nat) + 18446744073709551568) mod 2 ^ 64)
        /\ (((V 36%nat) - 5) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab1c M')
        /\ (forall x, In x KS_ab10P6_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 5
        /\ bv_unsigned (getr R' (reg 29)) = (Z.land (V 33%nat) 7)
        /\ (((V 37%nat) + 18446744073709551568) mod 2 ^ 64) < 10
        /\ (((V 36%nat) - 1) mod 2 ^ 64) < 1
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab60 M')
        /\ (forall x, In x KS_ab10P6_3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 37%nat) - 48)
        /\ bv_unsigned (getr R' (reg 29)) = (Z.land (V 33%nat) 7)
        /\ 10 <= (((V 37%nat) + 18446744073709551568) mod 2 ^ 64)
        /\ (((V 36%nat) - 1) mod 2 ^ 64) < 1
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab60 M')
        /\ (forall x, In x KS_ab10P6_4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ bv_unsigned (getr R' (reg 12)) = (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255)
        /\ bv_unsigned (getr R' (reg 29)) = (Z.land (8185 / 2 ^ ((((V 37%nat) + 18446744073709551571) mod 2 ^ 64) mod 64)) 1)
        /\ (((Z.land (8185 / 2 ^ ((((V 37%nat) + 18446744073709551571) mod 2 ^ 64) mod 64)) 1) - 0) mod 2 ^ 64) < 1
        /\ (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255) < 13
        /\ (((V 36%nat) - 0) mod 2 ^ 64) < 1
        /\ 1 <= (((V 36%nat) - 1) mod 2 ^ 64)
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbaab4 M')
        /\ (forall x, In x KS_ab10P6_5 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 12)) = ((((4 * (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255)) mod 2 ^ 64) + 146496) mod 2 ^ 64)
        /\ bv_unsigned (getr R' (reg 29)) = (Z.land (8185 / 2 ^ ((((V 37%nat) + 18446744073709551571) mod 2 ^ 64) mod 64)) 1)
        /\ 1 <= (((Z.land (8185 / 2 ^ ((((V 37%nat) + 18446744073709551571) mod 2 ^ 64) mod 64)) 1) - 0) mod 2 ^ 64)
        /\ (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255) < 13
        /\ (((V 36%nat) - 0) mod 2 ^ 64) < 1
        /\ 1 <= (((V 36%nat) - 1) mod 2 ^ 64)
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab60 M')
        /\ (forall x, In x KS_ab10P6_6 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ bv_unsigned (getr R' (reg 12)) = (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255)
        /\ getr R' (reg 29) = Z_to_bv 64 ((V 37%nat) - 45)
        /\ 13 <= (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255)
        /\ (((V 36%nat) - 0) mod 2 ^ 64) < 1
        /\ 1 <= (((V 36%nat) - 1) mod 2 ^ 64)
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab1c M')
        /\ (forall x, In x KS_ab10P6_7 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ 1 <= (((V 36%nat) - 0) mod 2 ^ 64)
        /\ 1 <= (((V 36%nat) - 1) mod 2 ^ 64)
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G5 G6 G7 G10 G11 G12 G13 G14 G15 G16 G17 G28 pvzI6 pvzI7 pvzI8 K3 pvzI9 K5 pvzI10.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K1l; move K1l before pvzI7; pose proof (proj2 pvzI7) as K1r; move K1r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K2l; move K2l before pvzI8; pose proof (proj2 pvzI8) as K2r; move K2r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K4l; move K4l before pvzI9; pose proof (proj2 pvzI9) as K4r; move K4r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E Pab10P6.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pab10P6.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pab10P6.kn0).
  { unfold know_ok, Pab10P6.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K6l K6r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K1l K1r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K2l K2r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K6l K6r) | evalEk ZA ltac:(clear - HV37l HV37r K4l K4r) | clear - HV33l HV33r K0l K0r K6l K6r; lia | clear - HV33l HV33r K0l K0r K6l K6r; lia | byte_tac ltac:(clear - HV37l HV37r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K6l K6r; lia | clear - HV33l HV33r K0l K0r K6l K6r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K6l K6r) | clear; lia | exact (conj K6l K6r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pab10P6.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pab10P6.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pab10P6.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc Pab10P6.ps0) with 0xbab1c in Hms. change (SR.ps_regs Pab10P6.ps0) with (map (fun i => (i, nth i Pab10P6.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P6.ps0) with Pab10P6.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P6.regs0 Pab10P6.regs_out0 60 KS_ab10P6_0 KS_ab10P6_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P6.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P6.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pab10P6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P6.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P6.regs_out0 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P6.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. left.
    change (SR.ps_pc Pab10P6.ps1) with 0xbab60 in Hms. change (SR.ps_regs Pab10P6.ps1) with (map (fun i => (i, nth i Pab10P6.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P6.ps1) with Pab10P6.cells1 in Hcells. unfold Pab10P6.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P6.regs0 Pab10P6.regs_out1 60 KS_ab10P6_1 KS_ab10P6_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P6.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P6.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P6.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P6.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P6.regs_out1 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P6.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. left.
    change (SR.ps_pc Pab10P6.ps2) with 0xbab1c in Hms. change (SR.ps_regs Pab10P6.ps2) with (map (fun i => (i, nth i Pab10P6.regs_out2 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P6.ps2) with Pab10P6.cells2 in Hcells. unfold Pab10P6.cells2 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P6.regs0 Pab10P6.regs_out2 60 KS_ab10P6_2 KS_ab10P6_2_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P6.regs_out2 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P6.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P6.regs_out2 E' R' 11 Hregs) by (clear; lia). cbn [nth Pab10P6.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P6.regs_out2 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P6.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P6.regs_out2 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P6.regs_out2]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. left.
    change (SR.ps_pc Pab10P6.ps3) with 0xbab60 in Hms. change (SR.ps_regs Pab10P6.ps3) with (map (fun i => (i, nth i Pab10P6.regs_out3 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P6.ps3) with Pab10P6.cells3 in Hcells. unfold Pab10P6.cells3 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P6.regs0 Pab10P6.regs_out3 60 KS_ab10P6_3 KS_ab10P6_3_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P6.regs_out3 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P6.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P6.regs_out3 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P6.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P6.regs_out3 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P6.regs_out3]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. left.
    change (SR.ps_pc Pab10P6.ps4) with 0xbab60 in Hms. change (SR.ps_regs Pab10P6.ps4) with (map (fun i => (i, nth i Pab10P6.regs_out4 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P6.ps4) with Pab10P6.cells4 in Hcells. unfold Pab10P6.cells4 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P6.regs0 Pab10P6.regs_out4 60 KS_ab10P6_4 KS_ab10P6_4_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P6.regs_out4 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P6.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P6.regs_out4 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P6.regs_out4]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg Pab10P6.regs_out4 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P6.regs_out4]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. left.
    change (SR.ps_pc Pab10P6.ps5) with 0xbaab4 in Hms. change (SR.ps_regs Pab10P6.ps5) with (map (fun i => (i, nth i Pab10P6.regs_out5 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P6.ps5) with Pab10P6.cells5 in Hcells. unfold Pab10P6.cells5 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P6.regs0 Pab10P6.regs_out5 60 KS_ab10P6_5 KS_ab10P6_5_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P6.regs_out5 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P6.regs_out5]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg Pab10P6.regs_out5 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P6.regs_out5]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. left.
    change (SR.ps_pc Pab10P6.ps6) with 0xbab60 in Hms. change (SR.ps_regs Pab10P6.ps6) with (map (fun i => (i, nth i Pab10P6.regs_out6 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P6.ps6) with Pab10P6.cells6 in Hcells. unfold Pab10P6.cells6 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P6.regs0 Pab10P6.regs_out6 60 KS_ab10P6_6 KS_ab10P6_6_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P6.regs_out6 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P6.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P6.regs_out6 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P6.regs_out6]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg Pab10P6.regs_out6 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P6.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right.
    change (SR.ps_pc Pab10P6.ps7) with 0xbab1c in Hms. change (SR.ps_regs Pab10P6.ps7) with (map (fun i => (i, nth i Pab10P6.regs_out7 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P6.ps7) with Pab10P6.cells7 in Hcells. unfold Pab10P6.cells7 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P6.regs0 Pab10P6.regs_out7 60 KS_ab10P6_7 KS_ab10P6_7_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P6.regs_out7 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P6.regs_out7]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P6.regs_out7 E' R' 11 Hregs) by (clear; lia). cbn [nth Pab10P6.regs_out7]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.

Module Pab10P7 := BndP_Eb_001S9.LibSegEb_ab10P7.
Definition KS_ab10P7_0 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P7.regs0 Pab10P7.regs_out0).
Lemma KS_ab10P7_0_ok : BG.kept_ok 60 Pab10P7.regs0 Pab10P7.regs_out0 KS_ab10P7_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P7_1 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P7.regs0 Pab10P7.regs_out1).
Lemma KS_ab10P7_1_ok : BG.kept_ok 60 Pab10P7.regs0 Pab10P7.regs_out1 KS_ab10P7_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P7_2 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P7.regs0 Pab10P7.regs_out2).
Lemma KS_ab10P7_2_ok : BG.kept_ok 60 Pab10P7.regs0 Pab10P7.regs_out2 KS_ab10P7_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P7_3 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P7.regs0 Pab10P7.regs_out3).
Lemma KS_ab10P7_3_ok : BG.kept_ok 60 Pab10P7.regs0 Pab10P7.regs_out3 KS_ab10P7_3 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P7_4 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P7.regs0 Pab10P7.regs_out4).
Lemma KS_ab10P7_4_ok : BG.kept_ok 60 Pab10P7.regs0 Pab10P7.regs_out4 KS_ab10P7_4 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P7_5 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P7.regs0 Pab10P7.regs_out5).
Lemma KS_ab10P7_5_ok : BG.kept_ok 60 Pab10P7.regs0 Pab10P7.regs_out5 KS_ab10P7_5 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P7_6 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P7.regs0 Pab10P7.regs_out6).
Lemma KS_ab10P7_6_ok : BG.kept_ok 60 Pab10P7.regs0 Pab10P7.regs_out6 KS_ab10P7_6 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10P7_7 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10P7.regs0 Pab10P7.regs_out7).
Lemma KS_ab10P7_7_ok : BG.kept_ok 60 Pab10P7.regs0 Pab10P7.regs_out7 KS_ab10P7_7 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ab10P7_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 16) -> getr R (reg 5) = Z_to_bv 64 13 -> getr R (reg 6) = Z_to_bv 64 2147450880 -> getr R (reg 7) = Z_to_bv 64 8185 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 (V 36%nat) -> getr R (reg 13) = Z_to_bv 64 (V 34%nat) -> getr R (reg 14) = Z_to_bv 64 5 -> getr R (reg 15) = Z_to_bv 64 10 -> getr R (reg 16) = Z_to_bv 64 2 -> getr R (reg 17) = Z_to_bv 64 1 -> getr R (reg 28) = Z_to_bv 64 146496 ->
  1 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 34%nat) <= 140737488355328 -> 0 <= (V 36%nat) <= 18446744073709551615 -> L5.u8_at RSEGS M (V 33%nat) (V 37%nat) ->
  0 <= (V 37%nat) <= 255 -> L5.u8_at RSEGS M (((V 33%nat) / 8) + 2147450880) 7 -> 0 <= Z.land (V 33%nat) 7 <= 6 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab1c M')
        /\ (forall x, In x KS_ab10P7_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 5
        /\ bv_unsigned (getr R' (reg 29)) = (Z.land (V 33%nat) 7)
        /\ (((V 37%nat) + 18446744073709551568) mod 2 ^ 64) < 10
        /\ (((V 36%nat) - 5) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab60 M')
        /\ (forall x, In x KS_ab10P7_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 37%nat) - 48)
        /\ bv_unsigned (getr R' (reg 29)) = (Z.land (V 33%nat) 7)
        /\ 10 <= (((V 37%nat) + 18446744073709551568) mod 2 ^ 64)
        /\ (((V 36%nat) - 5) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab1c M')
        /\ (forall x, In x KS_ab10P7_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 5
        /\ bv_unsigned (getr R' (reg 29)) = (Z.land (V 33%nat) 7)
        /\ (((V 37%nat) + 18446744073709551568) mod 2 ^ 64) < 10
        /\ (((V 36%nat) - 1) mod 2 ^ 64) < 1
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab60 M')
        /\ (forall x, In x KS_ab10P7_3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 37%nat) - 48)
        /\ bv_unsigned (getr R' (reg 29)) = (Z.land (V 33%nat) 7)
        /\ 10 <= (((V 37%nat) + 18446744073709551568) mod 2 ^ 64)
        /\ (((V 36%nat) - 1) mod 2 ^ 64) < 1
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab60 M')
        /\ (forall x, In x KS_ab10P7_4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ bv_unsigned (getr R' (reg 12)) = (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255)
        /\ bv_unsigned (getr R' (reg 29)) = (Z.land (8185 / 2 ^ ((((V 37%nat) + 18446744073709551571) mod 2 ^ 64) mod 64)) 1)
        /\ (((Z.land (8185 / 2 ^ ((((V 37%nat) + 18446744073709551571) mod 2 ^ 64) mod 64)) 1) - 0) mod 2 ^ 64) < 1
        /\ (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255) < 13
        /\ (((V 36%nat) - 0) mod 2 ^ 64) < 1
        /\ 1 <= (((V 36%nat) - 1) mod 2 ^ 64)
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbaab4 M')
        /\ (forall x, In x KS_ab10P7_5 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 12)) = ((((4 * (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255)) mod 2 ^ 64) + 146496) mod 2 ^ 64)
        /\ bv_unsigned (getr R' (reg 29)) = (Z.land (8185 / 2 ^ ((((V 37%nat) + 18446744073709551571) mod 2 ^ 64) mod 64)) 1)
        /\ 1 <= (((Z.land (8185 / 2 ^ ((((V 37%nat) + 18446744073709551571) mod 2 ^ 64) mod 64)) 1) - 0) mod 2 ^ 64)
        /\ (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255) < 13
        /\ (((V 36%nat) - 0) mod 2 ^ 64) < 1
        /\ 1 <= (((V 36%nat) - 1) mod 2 ^ 64)
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab60 M')
        /\ (forall x, In x KS_ab10P7_6 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ bv_unsigned (getr R' (reg 12)) = (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255)
        /\ getr R' (reg 29) = Z_to_bv 64 ((V 37%nat) - 45)
        /\ 13 <= (Z.land (((V 37%nat) + 18446744073709551571) mod 2 ^ 64) 255)
        /\ (((V 36%nat) - 0) mod 2 ^ 64) < 1
        /\ 1 <= (((V 36%nat) - 1) mod 2 ^ 64)
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xbaa70 M) (st fx' R' 0xbab1c M')
        /\ (forall x, In x KS_ab10P7_7 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ 1 <= (((V 36%nat) - 0) mod 2 ^ 64)
        /\ 1 <= (((V 36%nat) - 1) mod 2 ^ 64)
        /\ 1 <= (((V 36%nat) - 5) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G5 G6 G7 G10 G11 G12 G13 G14 G15 G16 G17 G28 pvzI6 pvzI7 pvzI8 K3 pvzI9 K5 pvzI10.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K1l; move K1l before pvzI7; pose proof (proj2 pvzI7) as K1r; move K1r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K2l; move K2l before pvzI8; pose proof (proj2 pvzI8) as K2r; move K2r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K4l; move K4l before pvzI9; pose proof (proj2 pvzI9) as K4r; move K4r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E Pab10P7.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pab10P7.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pab10P7.kn0).
  { unfold know_ok, Pab10P7.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K6l K6r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K1l K1r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K2l K2r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K6l K6r) | evalEk ZA ltac:(clear - HV37l HV37r K4l K4r) | clear - HV33l HV33r K0l K0r K6l K6r; lia | clear - HV33l HV33r K0l K0r K6l K6r; lia | byte_tac ltac:(clear - HV37l HV37r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K0l K0r K6l K6r; lia | clear - HV33l HV33r K0l K0r K6l K6r; lia | byte_tac ltac:(clear) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r K6l K6r) | clear; lia | exact (conj K6l K6r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pab10P7.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pab10P7.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pab10P7.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc Pab10P7.ps0) with 0xbab1c in Hms. change (SR.ps_regs Pab10P7.ps0) with (map (fun i => (i, nth i Pab10P7.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P7.ps0) with Pab10P7.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P7.regs0 Pab10P7.regs_out0 60 KS_ab10P7_0 KS_ab10P7_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P7.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P7.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pab10P7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P7.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P7.regs_out0 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P7.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. left.
    change (SR.ps_pc Pab10P7.ps1) with 0xbab60 in Hms. change (SR.ps_regs Pab10P7.ps1) with (map (fun i => (i, nth i Pab10P7.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P7.ps1) with Pab10P7.cells1 in Hcells. unfold Pab10P7.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P7.regs0 Pab10P7.regs_out1 60 KS_ab10P7_1 KS_ab10P7_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P7.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P7.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P7.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P7.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P7.regs_out1 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P7.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. left.
    change (SR.ps_pc Pab10P7.ps2) with 0xbab1c in Hms. change (SR.ps_regs Pab10P7.ps2) with (map (fun i => (i, nth i Pab10P7.regs_out2 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P7.ps2) with Pab10P7.cells2 in Hcells. unfold Pab10P7.cells2 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P7.regs0 Pab10P7.regs_out2 60 KS_ab10P7_2 KS_ab10P7_2_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P7.regs_out2 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P7.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P7.regs_out2 E' R' 11 Hregs) by (clear; lia). cbn [nth Pab10P7.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P7.regs_out2 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P7.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P7.regs_out2 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P7.regs_out2]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. left.
    change (SR.ps_pc Pab10P7.ps3) with 0xbab60 in Hms. change (SR.ps_regs Pab10P7.ps3) with (map (fun i => (i, nth i Pab10P7.regs_out3 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P7.ps3) with Pab10P7.cells3 in Hcells. unfold Pab10P7.cells3 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P7.regs0 Pab10P7.regs_out3 60 KS_ab10P7_3 KS_ab10P7_3_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P7.regs_out3 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P7.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P7.regs_out3 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P7.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P7.regs_out3 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P7.regs_out3]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. left.
    change (SR.ps_pc Pab10P7.ps4) with 0xbab60 in Hms. change (SR.ps_regs Pab10P7.ps4) with (map (fun i => (i, nth i Pab10P7.regs_out4 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P7.ps4) with Pab10P7.cells4 in Hcells. unfold Pab10P7.cells4 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P7.regs0 Pab10P7.regs_out4 60 KS_ab10P7_4 KS_ab10P7_4_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P7.regs_out4 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P7.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P7.regs_out4 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P7.regs_out4]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg Pab10P7.regs_out4 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P7.regs_out4]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. left.
    change (SR.ps_pc Pab10P7.ps5) with 0xbaab4 in Hms. change (SR.ps_regs Pab10P7.ps5) with (map (fun i => (i, nth i Pab10P7.regs_out5 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P7.ps5) with Pab10P7.cells5 in Hcells. unfold Pab10P7.cells5 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P7.regs0 Pab10P7.regs_out5 60 KS_ab10P7_5 KS_ab10P7_5_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P7.regs_out5 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P7.regs_out5]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg Pab10P7.regs_out5 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P7.regs_out5]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. left.
    change (SR.ps_pc Pab10P7.ps6) with 0xbab60 in Hms. change (SR.ps_regs Pab10P7.ps6) with (map (fun i => (i, nth i Pab10P7.regs_out6 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P7.ps6) with Pab10P7.cells6 in Hcells. unfold Pab10P7.cells6 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P7.regs0 Pab10P7.regs_out6 60 KS_ab10P7_6 KS_ab10P7_6_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P7.regs_out6 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P7.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P7.regs_out6 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10P7.regs_out6]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg Pab10P7.regs_out6 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10P7.regs_out6]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right. right. right. right.
    change (SR.ps_pc Pab10P7.ps7) with 0xbab1c in Hms. change (SR.ps_regs Pab10P7.ps7) with (map (fun i => (i, nth i Pab10P7.regs_out7 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10P7.ps7) with Pab10P7.cells7 in Hcells. unfold Pab10P7.cells7 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10P7.regs0 Pab10P7.regs_out7 60 KS_ab10P7_7 KS_ab10P7_7_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10P7.regs_out7 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10P7.regs_out7]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg Pab10P7.regs_out7 E' R' 11 Hregs) by (clear; lia). cbn [nth Pab10P7.regs_out7]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.

Module Pab10T0 := BndP_Eb_001S9.LibSegEb_ab10T0.
Definition KS_ab10T0 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10T0.regs0 Pab10T0.regs_out0).
Lemma KS_ab10T0_ok : BG.kept_ok 60 Pab10T0.regs0 Pab10T0.regs_out0 KS_ab10T0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ab10T0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 16) -> getr R (reg 5) = Z_to_bv 64 13 -> getr R (reg 6) = Z_to_bv 64 2147450880 -> getr R (reg 7) = Z_to_bv 64 8185 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 146496 -> getr R (reg 13) = Z_to_bv 64 (V 34%nat) -> getr R (reg 14) = Z_to_bv 64 5 -> getr R (reg 15) = Z_to_bv 64 10 -> getr R (reg 16) = Z_to_bv 64 2 -> getr R (reg 17) = Z_to_bv 64 1 -> getr R (reg 28) = Z_to_bv 64 146496 ->
  L5.img_clear M 65536 1306624 -> 1 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 34%nat) <= 140737488355328 -> L5KA.zeros_at M 2147469192 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xbaab4 M) (st fx' R' 0xbab1c M')
        /\ (forall x, In x KS_ab10T0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 29) = Z_to_bv 64 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G5 G6 G7 G10 G11 G12 G13 G14 G15 G16 G17 G28 K0 pvzI4 pvzI5 K3.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K1l; move K1l before pvzI4; pose proof (proj2 pvzI4) as K1r; move K1r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K2l; move K2l before pvzI5; pose proof (proj2 pvzI5) as K2r; move K2r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 35%nat. }
  assert (HR: regs_ok E Pab10T0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pab10T0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pab10T0.kn0).
  { unfold know_ok, Pab10T0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K1l K1r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K2l K2r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K3]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pab10T0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pab10T0.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pab10T0.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pab10T0.ps0) with 0xbab1c in Hms. change (SR.ps_regs Pab10T0.ps0) with (map (fun i => (i, nth i Pab10T0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pab10T0.ps0) with Pab10T0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10T0.regs0 Pab10T0.regs_out0 60 KS_ab10T0 KS_ab10T0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pab10T0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10T0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pab10T0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pab10T0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pab10T0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10T0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pab10T0.regs_out0 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10T0.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module Pab10T3 := BndP_Eb_001S9.LibSegEb_ab10T3.
Definition KS_ab10T3 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10T3.regs0 Pab10T3.regs_out0).
Lemma KS_ab10T3_ok : BG.kept_ok 60 Pab10T3.regs0 Pab10T3.regs_out0 KS_ab10T3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ab10T3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 16) -> getr R (reg 5) = Z_to_bv 64 13 -> getr R (reg 6) = Z_to_bv 64 2147450880 -> getr R (reg 7) = Z_to_bv 64 8185 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 146508 -> getr R (reg 13) = Z_to_bv 64 (V 34%nat) -> getr R (reg 14) = Z_to_bv 64 5 -> getr R (reg 15) = Z_to_bv 64 10 -> getr R (reg 16) = Z_to_bv 64 2 -> getr R (reg 17) = Z_to_bv 64 1 -> getr R (reg 28) = Z_to_bv 64 146496 ->
  L5.img_clear M 65536 1306624 -> 1 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 34%nat) <= 140737488355328 -> L5KA.zeros_at M 2147469193 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xbaab4 M) (st fx' R' 0xbab1c M')
        /\ (forall x, In x KS_ab10T3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 5
        /\ getr R' (reg 29) = Z_to_bv 64 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G5 G6 G7 G10 G11 G12 G13 G14 G15 G16 G17 G28 K0 pvzI4 pvzI5 K3.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K1l; move K1l before pvzI4; pose proof (proj2 pvzI4) as K1r; move K1r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K2l; move K2l before pvzI5; pose proof (proj2 pvzI5) as K2r; move K2r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 35%nat. }
  assert (HR: regs_ok E Pab10T3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pab10T3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pab10T3.kn0).
  { unfold know_ok, Pab10T3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K1l K1r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K2l K2r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K3]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pab10T3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pab10T3.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pab10T3.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pab10T3.ps0) with 0xbab1c in Hms. change (SR.ps_regs Pab10T3.ps0) with (map (fun i => (i, nth i Pab10T3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pab10T3.ps0) with Pab10T3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10T3.regs0 Pab10T3.regs_out0 60 KS_ab10T3 KS_ab10T3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pab10T3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10T3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pab10T3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pab10T3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pab10T3.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10T3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pab10T3.regs_out0 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10T3.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module Pab10T4 := BndP_Eb_001S9.LibSegEb_ab10T4.
Definition KS_ab10T4 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10T4.regs0 Pab10T4.regs_out0).
Lemma KS_ab10T4_ok : BG.kept_ok 60 Pab10T4.regs0 Pab10T4.regs_out0 KS_ab10T4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ab10T4_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 16) -> getr R (reg 5) = Z_to_bv 64 13 -> getr R (reg 6) = Z_to_bv 64 2147450880 -> getr R (reg 7) = Z_to_bv 64 8185 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 146512 -> getr R (reg 13) = Z_to_bv 64 (V 34%nat) -> getr R (reg 14) = Z_to_bv 64 5 -> getr R (reg 15) = Z_to_bv 64 10 -> getr R (reg 16) = Z_to_bv 64 2 -> getr R (reg 17) = Z_to_bv 64 1 -> getr R (reg 28) = Z_to_bv 64 146496 ->
  L5.img_clear M 65536 1306624 -> 1 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 34%nat) <= 140737488355328 -> L5KA.zeros_at M 2147469194 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xbaab4 M) (st fx' R' 0xbab1c M')
        /\ (forall x, In x KS_ab10T4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 5
        /\ getr R' (reg 29) = Z_to_bv 64 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G5 G6 G7 G10 G11 G12 G13 G14 G15 G16 G17 G28 K0 pvzI4 pvzI5 K3.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K1l; move K1l before pvzI4; pose proof (proj2 pvzI4) as K1r; move K1r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K2l; move K2l before pvzI5; pose proof (proj2 pvzI5) as K2r; move K2r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 35%nat. }
  assert (HR: regs_ok E Pab10T4.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pab10T4.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pab10T4.kn0).
  { unfold know_ok, Pab10T4.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K1l K1r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K2l K2r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K3]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pab10T4.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pab10T4.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pab10T4.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pab10T4.ps0) with 0xbab1c in Hms. change (SR.ps_regs Pab10T4.ps0) with (map (fun i => (i, nth i Pab10T4.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pab10T4.ps0) with Pab10T4.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10T4.regs0 Pab10T4.regs_out0 60 KS_ab10T4 KS_ab10T4_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pab10T4.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10T4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pab10T4.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pab10T4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pab10T4.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10T4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pab10T4.regs_out0 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10T4.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module Pab10T5 := BndP_Eb_001S9.LibSegEb_ab10T5.
Definition KS_ab10T5 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10T5.regs0 Pab10T5.regs_out0).
Lemma KS_ab10T5_ok : BG.kept_ok 60 Pab10T5.regs0 Pab10T5.regs_out0 KS_ab10T5 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ab10T5_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 16) -> getr R (reg 5) = Z_to_bv 64 13 -> getr R (reg 6) = Z_to_bv 64 2147450880 -> getr R (reg 7) = Z_to_bv 64 8185 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 146516 -> getr R (reg 13) = Z_to_bv 64 (V 34%nat) -> getr R (reg 14) = Z_to_bv 64 5 -> getr R (reg 15) = Z_to_bv 64 10 -> getr R (reg 16) = Z_to_bv 64 2 -> getr R (reg 17) = Z_to_bv 64 1 -> getr R (reg 28) = Z_to_bv 64 146496 ->
  L5.img_clear M 65536 1306624 -> 1 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 34%nat) <= 140737488355328 -> L5KA.zeros_at M 2147469194 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xbaab4 M) (st fx' R' 0xbab1c M')
        /\ (forall x, In x KS_ab10T5 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 5
        /\ getr R' (reg 29) = Z_to_bv 64 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G5 G6 G7 G10 G11 G12 G13 G14 G15 G16 G17 G28 K0 pvzI4 pvzI5 K3.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K1l; move K1l before pvzI4; pose proof (proj2 pvzI4) as K1r; move K1r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K2l; move K2l before pvzI5; pose proof (proj2 pvzI5) as K2r; move K2r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 35%nat. }
  assert (HR: regs_ok E Pab10T5.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pab10T5.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pab10T5.kn0).
  { unfold know_ok, Pab10T5.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K1l K1r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K2l K2r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K3]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pab10T5.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pab10T5.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pab10T5.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pab10T5.ps0) with 0xbab1c in Hms. change (SR.ps_regs Pab10T5.ps0) with (map (fun i => (i, nth i Pab10T5.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pab10T5.ps0) with Pab10T5.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10T5.regs0 Pab10T5.regs_out0 60 KS_ab10T5 KS_ab10T5_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pab10T5.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10T5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pab10T5.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pab10T5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pab10T5.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10T5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pab10T5.regs_out0 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10T5.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module Pab10T6 := BndP_Eb_001S9.LibSegEb_ab10T6.
Definition KS_ab10T6 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10T6.regs0 Pab10T6.regs_out0).
Lemma KS_ab10T6_ok : BG.kept_ok 60 Pab10T6.regs0 Pab10T6.regs_out0 KS_ab10T6 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ab10T6_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 16) -> getr R (reg 5) = Z_to_bv 64 13 -> getr R (reg 6) = Z_to_bv 64 2147450880 -> getr R (reg 7) = Z_to_bv 64 8185 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 146520 -> getr R (reg 13) = Z_to_bv 64 (V 34%nat) -> getr R (reg 14) = Z_to_bv 64 5 -> getr R (reg 15) = Z_to_bv 64 10 -> getr R (reg 16) = Z_to_bv 64 2 -> getr R (reg 17) = Z_to_bv 64 1 -> getr R (reg 28) = Z_to_bv 64 146496 ->
  L5.img_clear M 65536 1306624 -> 1 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 34%nat) <= 140737488355328 -> L5KA.zeros_at M 2147469195 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xbaab4 M) (st fx' R' 0xbab1c M')
        /\ (forall x, In x KS_ab10T6 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 5
        /\ getr R' (reg 29) = Z_to_bv 64 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G5 G6 G7 G10 G11 G12 G13 G14 G15 G16 G17 G28 K0 pvzI4 pvzI5 K3.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K1l; move K1l before pvzI4; pose proof (proj2 pvzI4) as K1r; move K1r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K2l; move K2l before pvzI5; pose proof (proj2 pvzI5) as K2r; move K2r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 35%nat. }
  assert (HR: regs_ok E Pab10T6.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pab10T6.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pab10T6.kn0).
  { unfold know_ok, Pab10T6.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K1l K1r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K2l K2r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K3]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pab10T6.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pab10T6.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pab10T6.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pab10T6.ps0) with 0xbab1c in Hms. change (SR.ps_regs Pab10T6.ps0) with (map (fun i => (i, nth i Pab10T6.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pab10T6.ps0) with Pab10T6.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10T6.regs0 Pab10T6.regs_out0 60 KS_ab10T6 KS_ab10T6_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pab10T6.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10T6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pab10T6.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pab10T6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pab10T6.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10T6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pab10T6.regs_out0 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10T6.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module Pab10T7 := BndP_Eb_001S9.LibSegEb_ab10T7.
Definition KS_ab10T7 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10T7.regs0 Pab10T7.regs_out0).
Lemma KS_ab10T7_ok : BG.kept_ok 60 Pab10T7.regs0 Pab10T7.regs_out0 KS_ab10T7 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ab10T7_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 16) -> getr R (reg 5) = Z_to_bv 64 13 -> getr R (reg 6) = Z_to_bv 64 2147450880 -> getr R (reg 7) = Z_to_bv 64 8185 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 146524 -> getr R (reg 13) = Z_to_bv 64 (V 34%nat) -> getr R (reg 14) = Z_to_bv 64 5 -> getr R (reg 15) = Z_to_bv 64 10 -> getr R (reg 16) = Z_to_bv 64 2 -> getr R (reg 17) = Z_to_bv 64 1 -> getr R (reg 28) = Z_to_bv 64 146496 ->
  L5.img_clear M 65536 1306624 -> 1 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 34%nat) <= 140737488355328 -> L5KA.zeros_at M 2147469195 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xbaab4 M) (st fx' R' 0xbab1c M')
        /\ (forall x, In x KS_ab10T7 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 5
        /\ getr R' (reg 29) = Z_to_bv 64 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G5 G6 G7 G10 G11 G12 G13 G14 G15 G16 G17 G28 K0 pvzI4 pvzI5 K3.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K1l; move K1l before pvzI4; pose proof (proj2 pvzI4) as K1r; move K1r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K2l; move K2l before pvzI5; pose proof (proj2 pvzI5) as K2r; move K2r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 35%nat. }
  assert (HR: regs_ok E Pab10T7.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pab10T7.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pab10T7.kn0).
  { unfold know_ok, Pab10T7.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K1l K1r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K2l K2r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K3]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pab10T7.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pab10T7.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pab10T7.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pab10T7.ps0) with 0xbab1c in Hms. change (SR.ps_regs Pab10T7.ps0) with (map (fun i => (i, nth i Pab10T7.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pab10T7.ps0) with Pab10T7.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10T7.regs0 Pab10T7.regs_out0 60 KS_ab10T7 KS_ab10T7_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pab10T7.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10T7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pab10T7.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pab10T7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pab10T7.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10T7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pab10T7.regs_out0 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10T7.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module Pab10T8 := BndP_Eb_001S9.LibSegEb_ab10T8.
Definition KS_ab10T8 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10T8.regs0 Pab10T8.regs_out0).
Lemma KS_ab10T8_ok : BG.kept_ok 60 Pab10T8.regs0 Pab10T8.regs_out0 KS_ab10T8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ab10T8_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 16) -> getr R (reg 5) = Z_to_bv 64 13 -> getr R (reg 6) = Z_to_bv 64 2147450880 -> getr R (reg 7) = Z_to_bv 64 8185 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 146528 -> getr R (reg 13) = Z_to_bv 64 (V 34%nat) -> getr R (reg 14) = Z_to_bv 64 5 -> getr R (reg 15) = Z_to_bv 64 10 -> getr R (reg 16) = Z_to_bv 64 2 -> getr R (reg 17) = Z_to_bv 64 1 -> getr R (reg 28) = Z_to_bv 64 146496 ->
  L5.img_clear M 65536 1306624 -> 1 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 34%nat) <= 140737488355328 -> L5KA.zeros_at M 2147469196 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xbaab4 M) (st fx' R' 0xbab1c M')
        /\ (forall x, In x KS_ab10T8 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 5
        /\ getr R' (reg 29) = Z_to_bv 64 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G5 G6 G7 G10 G11 G12 G13 G14 G15 G16 G17 G28 K0 pvzI4 pvzI5 K3.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K1l; move K1l before pvzI4; pose proof (proj2 pvzI4) as K1r; move K1r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K2l; move K2l before pvzI5; pose proof (proj2 pvzI5) as K2r; move K2r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 35%nat. }
  assert (HR: regs_ok E Pab10T8.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pab10T8.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pab10T8.kn0).
  { unfold know_ok, Pab10T8.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K1l K1r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K2l K2r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K3]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pab10T8.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pab10T8.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pab10T8.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pab10T8.ps0) with 0xbab1c in Hms. change (SR.ps_regs Pab10T8.ps0) with (map (fun i => (i, nth i Pab10T8.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pab10T8.ps0) with Pab10T8.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10T8.regs0 Pab10T8.regs_out0 60 KS_ab10T8 KS_ab10T8_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pab10T8.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10T8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pab10T8.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pab10T8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pab10T8.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10T8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pab10T8.regs_out0 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10T8.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module Pab10T9 := BndP_Eb_001S9.LibSegEb_ab10T9.
Definition KS_ab10T9 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10T9.regs0 Pab10T9.regs_out0).
Lemma KS_ab10T9_ok : BG.kept_ok 60 Pab10T9.regs0 Pab10T9.regs_out0 KS_ab10T9 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ab10T9_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 16) -> getr R (reg 5) = Z_to_bv 64 13 -> getr R (reg 6) = Z_to_bv 64 2147450880 -> getr R (reg 7) = Z_to_bv 64 8185 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 146532 -> getr R (reg 13) = Z_to_bv 64 (V 34%nat) -> getr R (reg 14) = Z_to_bv 64 5 -> getr R (reg 15) = Z_to_bv 64 10 -> getr R (reg 16) = Z_to_bv 64 2 -> getr R (reg 17) = Z_to_bv 64 1 -> getr R (reg 28) = Z_to_bv 64 146496 ->
  L5.img_clear M 65536 1306624 -> 1 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 34%nat) <= 140737488355328 -> L5KA.zeros_at M 2147469196 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xbaab4 M) (st fx' R' 0xbab1c M')
        /\ (forall x, In x KS_ab10T9 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 5
        /\ getr R' (reg 29) = Z_to_bv 64 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G5 G6 G7 G10 G11 G12 G13 G14 G15 G16 G17 G28 K0 pvzI4 pvzI5 K3.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K1l; move K1l before pvzI4; pose proof (proj2 pvzI4) as K1r; move K1r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K2l; move K2l before pvzI5; pose proof (proj2 pvzI5) as K2r; move K2r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 35%nat. }
  assert (HR: regs_ok E Pab10T9.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pab10T9.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pab10T9.kn0).
  { unfold know_ok, Pab10T9.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K1l K1r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K2l K2r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K3]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pab10T9.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pab10T9.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pab10T9.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pab10T9.ps0) with 0xbab1c in Hms. change (SR.ps_regs Pab10T9.ps0) with (map (fun i => (i, nth i Pab10T9.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pab10T9.ps0) with Pab10T9.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10T9.regs0 Pab10T9.regs_out0 60 KS_ab10T9 KS_ab10T9_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pab10T9.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10T9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pab10T9.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pab10T9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pab10T9.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10T9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pab10T9.regs_out0 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10T9.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module Pab10T10 := BndP_Eb_001S9.LibSegEb_ab10T10.
Definition KS_ab10T10 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10T10.regs0 Pab10T10.regs_out0).
Lemma KS_ab10T10_ok : BG.kept_ok 60 Pab10T10.regs0 Pab10T10.regs_out0 KS_ab10T10 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ab10T10_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 16) -> getr R (reg 5) = Z_to_bv 64 13 -> getr R (reg 6) = Z_to_bv 64 2147450880 -> getr R (reg 7) = Z_to_bv 64 8185 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 146536 -> getr R (reg 13) = Z_to_bv 64 (V 34%nat) -> getr R (reg 14) = Z_to_bv 64 5 -> getr R (reg 15) = Z_to_bv 64 10 -> getr R (reg 16) = Z_to_bv 64 2 -> getr R (reg 17) = Z_to_bv 64 1 -> getr R (reg 28) = Z_to_bv 64 146496 ->
  L5.img_clear M 65536 1306624 -> 1 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 34%nat) <= 140737488355328 -> L5KA.zeros_at M 2147469197 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xbaab4 M) (st fx' R' 0xbab1c M')
        /\ (forall x, In x KS_ab10T10 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 5
        /\ getr R' (reg 29) = Z_to_bv 64 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G5 G6 G7 G10 G11 G12 G13 G14 G15 G16 G17 G28 K0 pvzI4 pvzI5 K3.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K1l; move K1l before pvzI4; pose proof (proj2 pvzI4) as K1r; move K1r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K2l; move K2l before pvzI5; pose proof (proj2 pvzI5) as K2r; move K2r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 35%nat. }
  assert (HR: regs_ok E Pab10T10.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pab10T10.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pab10T10.kn0).
  { unfold know_ok, Pab10T10.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K1l K1r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K2l K2r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K3]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pab10T10.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pab10T10.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pab10T10.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pab10T10.ps0) with 0xbab1c in Hms. change (SR.ps_regs Pab10T10.ps0) with (map (fun i => (i, nth i Pab10T10.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pab10T10.ps0) with Pab10T10.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10T10.regs0 Pab10T10.regs_out0 60 KS_ab10T10 KS_ab10T10_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pab10T10.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10T10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pab10T10.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pab10T10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pab10T10.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10T10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pab10T10.regs_out0 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10T10.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module Pab10T11 := BndP_Eb_001S9.LibSegEb_ab10T11.
Definition KS_ab10T11 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10T11.regs0 Pab10T11.regs_out0).
Lemma KS_ab10T11_ok : BG.kept_ok 60 Pab10T11.regs0 Pab10T11.regs_out0 KS_ab10T11 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ab10T11_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 16) -> getr R (reg 5) = Z_to_bv 64 13 -> getr R (reg 6) = Z_to_bv 64 2147450880 -> getr R (reg 7) = Z_to_bv 64 8185 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 146540 -> getr R (reg 13) = Z_to_bv 64 (V 34%nat) -> getr R (reg 14) = Z_to_bv 64 5 -> getr R (reg 15) = Z_to_bv 64 10 -> getr R (reg 16) = Z_to_bv 64 2 -> getr R (reg 17) = Z_to_bv 64 1 -> getr R (reg 28) = Z_to_bv 64 146496 ->
  L5.img_clear M 65536 1306624 -> 1 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 34%nat) <= 140737488355328 -> L5KA.zeros_at M 2147469197 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xbaab4 M) (st fx' R' 0xbab1c M')
        /\ (forall x, In x KS_ab10T11 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 5
        /\ getr R' (reg 29) = Z_to_bv 64 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G5 G6 G7 G10 G11 G12 G13 G14 G15 G16 G17 G28 K0 pvzI4 pvzI5 K3.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K1l; move K1l before pvzI4; pose proof (proj2 pvzI4) as K1r; move K1r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K2l; move K2l before pvzI5; pose proof (proj2 pvzI5) as K2r; move K2r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 35%nat. }
  assert (HR: regs_ok E Pab10T11.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pab10T11.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pab10T11.kn0).
  { unfold know_ok, Pab10T11.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K1l K1r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K2l K2r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K3]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pab10T11.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pab10T11.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pab10T11.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pab10T11.ps0) with 0xbab1c in Hms. change (SR.ps_regs Pab10T11.ps0) with (map (fun i => (i, nth i Pab10T11.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pab10T11.ps0) with Pab10T11.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10T11.regs0 Pab10T11.regs_out0 60 KS_ab10T11 KS_ab10T11_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pab10T11.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10T11.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pab10T11.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pab10T11.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pab10T11.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10T11.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pab10T11.regs_out0 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10T11.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module Pab10T12 := BndP_Eb_001S9.LibSegEb_ab10T12.
Definition KS_ab10T12 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10T12.regs0 Pab10T12.regs_out0).
Lemma KS_ab10T12_ok : BG.kept_ok 60 Pab10T12.regs0 Pab10T12.regs_out0 KS_ab10T12 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ab10T12_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 16) -> getr R (reg 5) = Z_to_bv 64 13 -> getr R (reg 6) = Z_to_bv 64 2147450880 -> getr R (reg 7) = Z_to_bv 64 8185 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 146544 -> getr R (reg 13) = Z_to_bv 64 (V 34%nat) -> getr R (reg 14) = Z_to_bv 64 5 -> getr R (reg 15) = Z_to_bv 64 10 -> getr R (reg 16) = Z_to_bv 64 2 -> getr R (reg 17) = Z_to_bv 64 1 -> getr R (reg 28) = Z_to_bv 64 146496 ->
  L5.img_clear M 65536 1306624 -> 1 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 34%nat) <= 140737488355328 -> L5.u8_at RSEGS M 2147469198 4 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xbaab4 M) (st fx' R' 0xbab1c M')
        /\ (forall x, In x KS_ab10T12 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 5
        /\ getr R' (reg 29) = Z_to_bv 64 4
        /\ getr R' (reg 30) = Z_to_bv 64 3).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G5 G6 G7 G10 G11 G12 G13 G14 G15 G16 G17 G28 K0 pvzI4 pvzI5 K3.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K1l; move K1l before pvzI4; pose proof (proj2 pvzI4) as K1r; move K1r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K2l; move K2l before pvzI5; pose proof (proj2 pvzI5) as K2r; move K2r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 35%nat. }
  assert (HR: regs_ok E Pab10T12.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pab10T12.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pab10T12.kn0).
  { unfold know_ok, Pab10T12.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K1l K1r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K2l K2r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K3]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pab10T12.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pab10T12.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pab10T12.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pab10T12.ps0) with 0xbab1c in Hms. change (SR.ps_regs Pab10T12.ps0) with (map (fun i => (i, nth i Pab10T12.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pab10T12.ps0) with Pab10T12.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10T12.regs0 Pab10T12.regs_out0 60 KS_ab10T12 KS_ab10T12_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pab10T12.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10T12.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pab10T12.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pab10T12.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pab10T12.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10T12.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pab10T12.regs_out0 E' R' 29 Hregs) by (clear; lia). cbn [nth Pab10T12.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pab10T12.regs_out0 E' R' 30 Hregs) by (clear; lia). cbn [nth Pab10T12.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module Pab10F := BndP_Eb_000S9.LibSegEb_ab10F.
Definition KS_ab10F_0 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10F.regs0 Pab10F.regs_out0).
Lemma KS_ab10F_0_ok : BG.kept_ok 60 Pab10F.regs0 Pab10F.regs_out0 KS_ab10F_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ab10F_1 : list nat := Eval vm_compute in (BG.kept_list 60 Pab10F.regs0 Pab10F.regs_out1).
Lemma KS_ab10F_1_ok : BG.kept_ok 60 Pab10F.regs0 Pab10F.regs_out1 KS_ab10F_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ab10F_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 16) -> getr R (reg 5) = Z_to_bv 64 13 -> getr R (reg 6) = Z_to_bv 64 2147450880 -> getr R (reg 7) = Z_to_bv 64 8185 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 (V 36%nat) -> getr R (reg 13) = Z_to_bv 64 (V 34%nat) -> getr R (reg 14) = Z_to_bv 64 5 -> getr R (reg 15) = Z_to_bv 64 10 -> getr R (reg 16) = Z_to_bv 64 2 -> getr R (reg 17) = Z_to_bv 64 1 -> getr R (reg 28) = Z_to_bv 64 146496 ->
  1 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 34%nat) <= 140737488355328 -> 0 <= (V 36%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xbab1c M) (st fx' R' 0xbaa70 M')
        /\ (forall x, In x KS_ab10F_0 -> getr R' (reg x) = getr R (reg x))
        /\ (V 33%nat) < (V 34%nat))
      \/ (msteps RSEGS (st fx R 0xbab1c M) (st fx' R' 0xbab60 M')
        /\ (forall x, In x KS_ab10F_1 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 10)) = (if (((V 36%nat) + 18446744073709551611) mod 2 ^ 64) <? 1 then 1 else 0)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 36%nat) - 5)
        /\ (V 34%nat) <= (V 33%nat))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G6 G7 G10 G11 G12 G13 G14 G15 G16 G17 G28 pvzI5 pvzI6 pvzI7.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K1l; move K1l before pvzI6; pose proof (proj2 pvzI6) as K1r; move K1r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E Pab10F.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pab10F.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pab10F.kn0).
  { unfold know_ok, Pab10F.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K1l K1r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K2l K2r) | exact (conj K2l K2r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pab10F.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pab10F.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pab10F.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc Pab10F.ps0) with 0xbaa70 in Hms. change (SR.ps_regs Pab10F.ps0) with (map (fun i => (i, nth i Pab10F.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10F.ps0) with Pab10F.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10F.regs0 Pab10F.regs_out0 60 KS_ab10F_0 KS_ab10F_0_ok HR Hag Hregs j Hj). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  - right.
    change (SR.ps_pc Pab10F.ps1) with 0xbab60 in Hms. change (SR.ps_regs Pab10F.ps1) with (map (fun i => (i, nth i Pab10F.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells Pab10F.ps1) with Pab10F.cells1 in Hcells. unfold Pab10F.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10F.regs0 Pab10F.regs_out1 60 KS_ab10F_1 KS_ab10F_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg Pab10F.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth Pab10F.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg Pab10F.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth Pab10F.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
Qed.

Module Pab10X := BndP_Eb_001S9.LibSegEb_ab10X.
Definition KS_ab10X : list nat := Eval vm_compute in (BG.kept_list 60 Pab10X.regs0 Pab10X.regs_out0).
Lemma KS_ab10X_ok : BG.kept_ok 60 Pab10X.regs0 Pab10X.regs_out0 KS_ab10X = true. Proof. vm_compute. reflexivity. Qed.
Lemma ab10X_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 16) ->
  140735332487184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 40%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xbab60 M) (st fx' R' 0xbab68 M')
        /\ (forall x, In x KS_ab10X -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)).
Proof.
  intros pvzI1 pvzI2 G2 pvzI3 K1 K2.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV40l; move HV40l before pvzI2; pose proof (proj2 pvzI2) as HV40r; move HV40r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as K0l; move K0l before pvzI3; pose proof (proj2 pvzI3) as K0r; move K0r before pvzI3; clear pvzI3.
  set (vz_2 := V 2%nat) in *. set (vz_40 := V 40%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 40%nat => Z_to_bv 64 vz_40 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 40%nat => vz_40 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 41%nat. }
  assert (HR: regs_ok E Pab10X.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pab10X.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pab10X.kn0).
  { unfold know_ok, Pab10X.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pab10X.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pab10X.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pab10X.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pab10X.ps0) with 0xbab68 in Hms. change (SR.ps_regs Pab10X.ps0) with (map (fun i => (i, nth i Pab10X.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pab10X.ps0) with Pab10X.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pab10X.regs0 Pab10X.regs_out0 60 KS_ab10X KS_ab10X_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pab10X.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pab10X.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pab10X.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth Pab10X.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

End PMBB10P.
