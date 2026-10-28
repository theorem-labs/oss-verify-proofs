(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BigLinkZA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0PlanKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanPlanCore
     BigLinkBase. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import BigLinkGlue_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import L5Kn_u L5KnA_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.seg Require LibSegBs_xgA0_u LibSegBs_xgA1_u LibSegBs_xgA2_u LibSegBs_xgC1_u LibSegBs_xgC2_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PMSXGP.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
  intros A Pz. rewrite (BG.word_of_unsigned (edenot E e) (z mod BL.MM) (L5KA.zpolyA_sound E Vz e z A Pz)).
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, BL.MM. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof. intros K Ha Hv ->. eapply L5K.u64_of_KWord8; eauto. Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof. intros K Ha Hv ->. eapply L5K.u32_of_KWord4; eauto. Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof. intros K Ha Hv Hr ->. eapply L5K.u8_of_KWord1; eauto. Qed.
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
(* [comment removed for export] *)
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
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac solve_modk k :=
  repeat match goal with |- context [(?x mod 18446744073709551616) / _] => rewrite (Z.mod_small x 18446744073709551616) by (k; zfacts; lia) end;
  first [ rewrite Z.mod_small; [ first [reflexivity | k; lia] | k; L5K.zrange_tac ]
        | symmetry; eapply (Z.mod_unique_pos _ _ (-1)); k; unfold BL.MM; lia
        | symmetry; eapply (Z.mod_unique_pos _ _ 1); k; unfold BL.MM; lia ].
(* [comment removed for export] *)
Local Ltac pvz_hg tac := lazymatch goal with |- ?G0 => let PG := fresh "PGoal" in set (PG := G0); tac; subst PG end.
Local Ltac pvz_fold B k := lazymatch B with | ?A2 /\ ?B2 => pvz_fold B2 ltac:(fun T2 => let T := fresh "pvzT" in pose (T := A2 /\ T2); k T) | _ => k B end.
Local Ltac pvz_linconj := lazymatch goal with |- ?A /\ ?B => pvz_fold B ltac:(fun T => change_no_check (A /\ T)) | _ => idtac end.
Local Ltac pvz_unfold ZA := lazymatch type of ZA with forall j, _ = ?f j => tryif is_var f then unfold f else idtac | _ => idtac end.
Tactic Notation "evalEk" constr(ZA) tactic(k) :=
  L5K.norm_expr; eapply L5KA.zpolyA_val; [ apply (L5K.zagree_all _ _ _ ZA) | cbn [L5KA.zpolyA]; pvz_unfold ZA; reflexivity | solve_modk k ].
Tactic Notation "evalEk'" constr(ZA) constr(AG) tactic(k) :=
  L5K.norm_expr; eapply L5KA.zpolyA_val;
  [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity] | cbn [L5KA.zpolyA]; pvz_unfold ZA; reflexivity | solve_modk k ].
(* [comment removed for export] *)
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
(* [comment removed for export] *)
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
(* [comment removed for export] *)
Local Ltac den_tac := first [reflexivity | lia | idtac].
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac apc_norm :=
  repeat match goal with
  | |- context [APC.eadd ?a ?b] => let t := eval vm_compute in (APC.eadd a b) in change (APC.eadd a b) with t
  | |- context [APC.esub ?a ?b] => let t := eval vm_compute in (APC.esub a b) in change (APC.esub a b) with t
  | |- context [APC.escale ?c ?e] => let t := eval vm_compute in (APC.escale c e) in change (APC.escale c e) with t
  | |- context [APC.eaddz ?a ?z] => let t := eval vm_compute in (APC.eaddz a z) in change (APC.eaddz a z) with t
  end.
(* [comment removed for export] *)
Local Ltac zp_norm := repeat (match goal with |- context [(?a <=? ?b) && (?c <? ?d)] => let r := eval vm_compute in ((a <=? b) && (c <? d)) in change ((a <=? b) && (c <? d)) with r end);
  repeat (match goal with |- context [2 ^ ?s] => let r := eval vm_compute in (2 ^ s) in change (2 ^ s) with r end); lazy beta iota zeta.
Local Ltac zp_mods := repeat match goal with |- context [(?x mod 18446744073709551616) / _] => rewrite (Z.mod_small x 18446744073709551616) by (zfacts; lia) end.
Local Ltac slotP ZA :=
  first [ assumption | reflexivity
        | (etransitivity; [eassumption|]; symmetry; eapply word_of_zpoly; [apply (L5K.zagree_all _ _ _ ZA) | cbn [L5KA.zpolyA]; pvz_unfold ZA; zp_norm; f_equal; zp_mods; first [reflexivity | clear; zfacts; lia | zfacts; lia]]) ].
(* [comment removed for export] *)
Local Ltac wordP' ZA AG :=
  eapply word_of_zpoly; [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity]
                        | cbn [L5KA.zpolyA]; pvz_unfold ZA; zp_norm; f_equal; zp_mods; first [reflexivity | clear; zfacts; lia | zfacts; lia] ].
(* [comment removed for export] *)
Module PxgA0 := LibSegBs_xgA0_u.
Definition KS_xgA0 : list nat := Eval vm_compute in (BG.kept_list 48 PxgA0.regs0 PxgA0.regs_out0).
Lemma KS_xgA0_ok : BG.kept_ok 48 PxgA0.regs0 PxgA0.regs_out0 KS_xgA0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma xgA0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 (V 37%nat) -> getr R (reg 12) = Z_to_bv 64 16384 ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 140735332483152 <= (V 36%nat) <= 140737488355072 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 256 <= ((V 2%nat) - 80)) -> L5.img_clear M 65536 754672 -> L5.u64_at RSEGS M (V 36%nat) 740552 ->
  L5.u64_at RSEGS M ((V 36%nat) + 24) (V 33%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 32) (V 33%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 48) 0 -> L5.u64_at RSEGS M ((V 36%nat) + 88) (V 33%nat) ->
  L5.u32_at RSEGS M ((V 36%nat) + 96) 8 -> 4096 <= (V 33%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 80) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 80) <= i < ((V 2%nat) - 80) + 80) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x5d574 M) (st fx' R' 0x5d67c M')
        /\ (forall x, In x KS_xgA0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 18446744073709551615
        /\ getr R' (reg 12) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 382476
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G10 G11 G12 pvzI5 K1 K2 pvzI6 K4 K5 K6 K7 K8 K9 K10 K11 K12 pvzI7.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K13l; move K13l before pvzI7; pose proof (proj2 pvzI7) as K13r; move K13r before pvzI7; clear pvzI7.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 36%nat => vz_36 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PxgA0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PxgA0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PxgA0.kn0).
  { unfold know_ok, PxgA0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear - HV33l HV33r K13l K13r) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear - HV33l HV33r K13l K13r) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear - HV33l HV33r K13l K13r) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K13l K13r) | exact (conj K13l K13r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PxgA0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PxgA0.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 80) <= bv_unsigned a < (vz_2 - 80) + 80) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PxgA0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PxgA0.ps0) with 0x5d67c in Hms. change (SR.ps_regs PxgA0.ps0) with (map (fun i => (i, nth i PxgA0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PxgA0.ps0) with PxgA0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PxgA0.regs0 PxgA0.regs_out0 48 KS_xgA0 KS_xgA0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PxgA0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PxgA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgA0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PxgA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgA0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PxgA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgA0.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PxgA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PxgA1 := LibSegBs_xgA1_u.
Definition KS_xgA1 : list nat := Eval vm_compute in (BG.kept_list 48 PxgA1.regs0 PxgA1.regs_out0).
Lemma KS_xgA1_ok : BG.kept_ok 48 PxgA1.regs0 PxgA1.regs_out0 KS_xgA1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma xgA1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 (V 37%nat) -> getr R (reg 12) = Z_to_bv 64 16384 ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 140735332483152 <= (V 36%nat) <= 140737488355072 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 256 <= ((V 2%nat) - 80)) -> L5.img_clear M 65536 754672 -> L5.u64_at RSEGS M (V 36%nat) 740552 ->
  L5.u64_at RSEGS M ((V 36%nat) + 24) (V 33%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 32) ((V 33%nat) + (V 35%nat)) -> L5.u64_at RSEGS M ((V 36%nat) + 48) 0 -> L5.u64_at RSEGS M ((V 36%nat) + 88) ((V 33%nat) + (V 35%nat)) ->
  L5.u32_at RSEGS M ((V 36%nat) + 96) 8 -> 4096 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 16384 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 80) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 80) <= i < ((V 2%nat) - 80) + 80) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x5d574 M) (st fx' R' 0xab884 M')
        /\ (forall x, In x KS_xgA1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 382536
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = Z_to_bv 64 0
        /\ getr R' (reg 9) = Z_to_bv 64 16384
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 2147483647
        /\ getr R' (reg 22) = Z_to_bv 64 18446744073709551615
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G10 G11 G12 pvzI6 K1 K2 pvzI7 K4 K5 K6 K7 K8 K9 K10 K11 K12 pvzI8 pvzI9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K13l; move K13l before pvzI8; pose proof (proj2 pvzI8) as K13r; move K13r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PxgA1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PxgA1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PxgA1.kn0).
  { unfold know_ok, PxgA1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear - HV33l HV33r K13l K13r) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear - HV33l HV33r K13l K13r HV35l HV35r K14l K14r) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear - HV33l HV33r K13l K13r HV35l HV35r K14l K14r) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K13l K13r) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PxgA1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PxgA1.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 80) <= bv_unsigned a < (vz_2 - 80) + 80) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PxgA1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PxgA1.ps0) with 0xab884 in Hms. change (SR.ps_regs PxgA1.ps0) with (map (fun i => (i, nth i PxgA1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PxgA1.ps0) with PxgA1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PxgA1.regs0 PxgA1.regs_out0 48 KS_xgA1 KS_xgA1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PxgA1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PxgA1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgA1.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PxgA1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgA1.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PxgA1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgA1.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PxgA1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgA1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PxgA1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgA1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PxgA1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgA1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PxgA1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgA1.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PxgA1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgA1.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PxgA1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgA1.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PxgA1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgA1.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PxgA1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgA1.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PxgA1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PxgA2 := LibSegBs_xgA2_u.
Definition KS_xgA2 : list nat := Eval vm_compute in (BG.kept_list 48 PxgA2.regs0 PxgA2.regs_out0).
Lemma KS_xgA2_ok : BG.kept_ok 48 PxgA2.regs0 PxgA2.regs_out0 KS_xgA2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma xgA2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 (V 37%nat) -> getr R (reg 12) = Z_to_bv 64 16384 ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 140735332483152 <= (V 36%nat) <= 140737488355072 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 256 <= ((V 2%nat) - 80)) -> L5.img_clear M 65536 754672 -> L5.u64_at RSEGS M (V 36%nat) 740552 ->
  L5.u64_at RSEGS M ((V 36%nat) + 24) (V 33%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 32) ((V 33%nat) + (V 35%nat)) -> L5.u64_at RSEGS M ((V 36%nat) + 48) 0 -> L5.u64_at RSEGS M ((V 36%nat) + 88) ((V 33%nat) + (V 35%nat)) ->
  L5.u32_at RSEGS M ((V 36%nat) + 96) 8 -> 4096 <= (V 33%nat) <= 140737488355328 -> 16385 <= (V 35%nat) <= 134217728 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 80) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 80) <= i < ((V 2%nat) - 80) + 80) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x5d574 M) (st fx' R' 0xab884 M')
        /\ (forall x, In x KS_xgA2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 382536
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = Z_to_bv 64 0
        /\ getr R' (reg 9) = Z_to_bv 64 16384
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 16384
        /\ getr R' (reg 21) = Z_to_bv 64 2147483647
        /\ getr R' (reg 22) = Z_to_bv 64 18446744073709551615
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G10 G11 G12 pvzI6 K1 K2 pvzI7 K4 K5 K6 K7 K8 K9 K10 K11 K12 pvzI8 pvzI9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K13l; move K13l before pvzI8; pose proof (proj2 pvzI8) as K13r; move K13r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PxgA2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PxgA2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PxgA2.kn0).
  { unfold know_ok, PxgA2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear - HV33l HV33r K13l K13r) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear - HV33l HV33r K13l K13r HV35l HV35r K14l K14r) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear - HV33l HV33r K13l K13r HV35l HV35r K14l K14r) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K13l K13r) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PxgA2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PxgA2.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 80) <= bv_unsigned a < (vz_2 - 80) + 80) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PxgA2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PxgA2.ps0) with 0xab884 in Hms. change (SR.ps_regs PxgA2.ps0) with (map (fun i => (i, nth i PxgA2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PxgA2.ps0) with PxgA2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PxgA2.regs0 PxgA2.regs_out0 48 KS_xgA2 KS_xgA2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PxgA2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PxgA2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgA2.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PxgA2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgA2.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PxgA2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgA2.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PxgA2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgA2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PxgA2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgA2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PxgA2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgA2.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PxgA2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgA2.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PxgA2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgA2.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PxgA2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgA2.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PxgA2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgA2.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PxgA2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PxgC1 := LibSegBs_xgC1_u.
Definition KS_xgC1 : list nat := Eval vm_compute in (BG.kept_list 48 PxgC1.regs0 PxgC1.regs_out0).
Lemma KS_xgC1_ok : BG.kept_ok 48 PxgC1.regs0 PxgC1.regs_out0 KS_xgC1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma xgC1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 0 -> getr R (reg 9) = Z_to_bv 64 16384 -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 16384 -> getr R (reg 21) = Z_to_bv 64 2147483647 -> getr R (reg 22) = Z_to_bv 64 18446744073709551615 ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 140735332483152 <= (V 36%nat) <= 140737488355072 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 256 <= ((V 2%nat) - 80)) -> L5.img_clear M 65536 754672 -> L5.u64_at RSEGS M (V 36%nat) 740552 ->
  L5.u64_at RSEGS M ((V 36%nat) + 24) (V 33%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 32) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 48) 0 -> L5.u64_at RSEGS M ((V 36%nat) + 88) (V 34%nat) ->
  L5.u32_at RSEGS M ((V 36%nat) + 96) 8 -> L5.writable RSEGS M ((V 36%nat) + 24) 8 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 38%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 39%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 41%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 42%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 44%nat) -> 4096 <= (V 33%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 80) -> ~ (((V 36%nat) + 24) <= bv_unsigned a < ((V 36%nat) + 24) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 80) <= i < ((V 2%nat) - 80) + 80) -> ~ (((V 36%nat) + 24) <= i < ((V 36%nat) + 24) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x5d648 M) (st fx' R' 0x5d67c M')
        /\ (forall x, In x KS_xgC1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 39%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 16384
        /\ getr R' (reg 11) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 24) ((V 33%nat) + 16384)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 39%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 41%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 42%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 44%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 G2 G8 G9 G19 G20 G21 G22 pvzI13 K1 K2 pvzI14 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 pvzI15.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV39l; move HV39l before pvzI7; pose proof (proj2 pvzI7) as HV39r; move HV39r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV40l; move HV40l before pvzI8; pose proof (proj2 pvzI8) as HV40r; move HV40r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV41l; move HV41l before pvzI9; pose proof (proj2 pvzI9) as HV41r; move HV41r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV42l; move HV42l before pvzI10; pose proof (proj2 pvzI10) as HV42r; move HV42r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV43l; move HV43l before pvzI11; pose proof (proj2 pvzI11) as HV43r; move HV43r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV44l; move HV44l before pvzI12; pose proof (proj2 pvzI12) as HV44r; move HV44r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K0l; move K0l before pvzI13; pose proof (proj2 pvzI13) as K0r; move K0r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K3l; move K3l before pvzI14; pose proof (proj2 pvzI14) as K3r; move K3r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K22l; move K22l before pvzI15; pose proof (proj2 pvzI15) as K22r; move K22r before pvzI15; clear pvzI15.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 41%nat => vz_41 | 42%nat => vz_42 | 43%nat => vz_43 | 44%nat => vz_44 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 45%nat. }
  assert (HR: regs_ok E PxgC1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PxgC1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PxgC1.kn0).
  { unfold know_ok, PxgC1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear - HV33l HV33r K22l K22r) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV37l HV37r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV39l HV39r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV41l HV41r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PxgC1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PxgC1.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 80) <= bv_unsigned a < (vz_2 - 80) + 80) -> ~ ((vz_36 + 24) <= bv_unsigned a < (vz_36 + 24) + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PxgC1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K3l K3r K5 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PxgC1.ps0) with 0x5d67c in Hms. change (SR.ps_regs PxgC1.ps0) with (map (fun i => (i, nth i PxgC1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PxgC1.ps0) with PxgC1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PxgC1.regs0 PxgC1.regs_out0 48 KS_xgC1 KS_xgC1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PxgC1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PxgC1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgC1.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PxgC1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgC1.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PxgC1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgC1.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PxgC1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgC1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PxgC1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgC1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PxgC1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgC1.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PxgC1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgC1.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PxgC1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgC1.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PxgC1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgC1.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PxgC1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgC1.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PxgC1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K22l K22r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV37l HV37r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV38l HV38r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV39l HV39r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV41l HV41r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV42l HV42r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PxgC2 := LibSegBs_xgC2_u.
Definition KS_xgC2 : list nat := Eval vm_compute in (BG.kept_list 48 PxgC2.regs0 PxgC2.regs_out0).
Lemma KS_xgC2_ok : BG.kept_ok 48 PxgC2.regs0 PxgC2.regs_out0 KS_xgC2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma xgC2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 0 -> getr R (reg 9) = Z_to_bv 64 16384 -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 35%nat) -> getr R (reg 21) = Z_to_bv 64 2147483647 -> getr R (reg 22) = Z_to_bv 64 18446744073709551615 ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 140735332483152 <= (V 36%nat) <= 140737488355072 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 256 <= ((V 2%nat) - 80)) -> L5.img_clear M 65536 754672 -> L5.u64_at RSEGS M (V 36%nat) 740552 ->
  L5.u64_at RSEGS M ((V 36%nat) + 24) (V 33%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 32) ((V 33%nat) + (V 35%nat)) -> L5.u64_at RSEGS M ((V 36%nat) + 48) 0 -> L5.u64_at RSEGS M ((V 36%nat) + 88) ((V 33%nat) + (V 35%nat)) ->
  L5.u32_at RSEGS M ((V 36%nat) + 96) 8 -> L5.writable RSEGS M ((V 36%nat) + 24) 8 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 38%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 39%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 41%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 42%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 44%nat) -> 4096 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 16383 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 80) -> ~ (((V 36%nat) + 24) <= bv_unsigned a < ((V 36%nat) + 24) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 80) <= i < ((V 2%nat) - 80) + 80) -> ~ (((V 36%nat) + 24) <= i < ((V 36%nat) + 24) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x5d648 M) (st fx' R' 0x5d67c M')
        /\ (forall x, In x KS_xgC2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 39%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 18446744073709551615
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + (V 35%nat))
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat))
        /\ getr R' (reg 18) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 382476
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 24) ((V 33%nat) + (V 35%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 39%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 41%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 42%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 44%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 G2 G8 G9 G19 G20 G21 G22 pvzI13 K1 K2 pvzI14 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 pvzI15 pvzI16.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV39l; move HV39l before pvzI7; pose proof (proj2 pvzI7) as HV39r; move HV39r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV40l; move HV40l before pvzI8; pose proof (proj2 pvzI8) as HV40r; move HV40r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV41l; move HV41l before pvzI9; pose proof (proj2 pvzI9) as HV41r; move HV41r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV42l; move HV42l before pvzI10; pose proof (proj2 pvzI10) as HV42r; move HV42r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV43l; move HV43l before pvzI11; pose proof (proj2 pvzI11) as HV43r; move HV43r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV44l; move HV44l before pvzI12; pose proof (proj2 pvzI12) as HV44r; move HV44r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K0l; move K0l before pvzI13; pose proof (proj2 pvzI13) as K0r; move K0r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K3l; move K3l before pvzI14; pose proof (proj2 pvzI14) as K3r; move K3r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K22l; move K22l before pvzI15; pose proof (proj2 pvzI15) as K22r; move K22r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K23l; move K23l before pvzI16; pose proof (proj2 pvzI16) as K23r; move K23r before pvzI16; clear pvzI16.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 41%nat => vz_41 | 42%nat => vz_42 | 43%nat => vz_43 | 44%nat => vz_44 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 45%nat. }
  assert (HR: regs_ok E PxgC2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PxgC2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PxgC2.kn0).
  { unfold know_ok, PxgC2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear - HV33l HV33r K22l K22r) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear - HV33l HV33r K22l K22r HV35l HV35r K23l K23r) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear - HV33l HV33r K22l K22r HV35l HV35r K23l K23r) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | clear - HV36l HV36r K3l K3r K5; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV37l HV37r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV39l HV39r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV41l HV41r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PxgC2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PxgC2.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 80) <= bv_unsigned a < (vz_2 - 80) + 80) -> ~ ((vz_36 + 24) <= bv_unsigned a < (vz_36 + 24) + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PxgC2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K3l K3r K5 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PxgC2.ps0) with 0x5d67c in Hms. change (SR.ps_regs PxgC2.ps0) with (map (fun i => (i, nth i PxgC2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PxgC2.ps0) with PxgC2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PxgC2.regs0 PxgC2.regs_out0 48 KS_xgC2 KS_xgC2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PxgC2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PxgC2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgC2.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PxgC2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgC2.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PxgC2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgC2.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PxgC2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgC2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PxgC2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgC2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PxgC2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgC2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PxgC2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgC2.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PxgC2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgC2.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PxgC2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgC2.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PxgC2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgC2.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PxgC2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgC2.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PxgC2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PxgC2.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PxgC2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV35l HV35r K23l K23r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K3l K3r K5) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K22l K22r HV35l HV35r K23l K23r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV37l HV37r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV38l HV38r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV39l HV39r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV41l HV41r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV42l HV42r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

End PMSXGP.
