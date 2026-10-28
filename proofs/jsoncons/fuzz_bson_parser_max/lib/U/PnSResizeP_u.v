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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.seg Require LibSegBs_rzS_u LibSegBs_rzL_u LibSegBs_rzTS_u LibSegBs_rzTL_u LibSegBs_apS0_u LibSegBs_apL0_u LibSegBs_fitS_u LibSegBs_fitL_u LibSegBs_apMS_u LibSegBs_apML_u LibSegBs_growS_u LibSegBs_growL_u LibSegBs_rec_u LibSegBs_pN_u LibSegBs_pDS_u LibSegBs_pDL_u LibSegBs_pF_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PMSRZP.
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
(* [comment removed for export] *)
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
Module PrzS := LibSegBs_rzS_u.
Definition KS_rzS_0 : list nat := Eval vm_compute in (BG.kept_list 48 PrzS.regs0 PrzS.regs_out0).
Lemma KS_rzS_0_ok : BG.kept_ok 48 PrzS.regs0 PrzS.regs_out0 KS_rzS_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_rzS_1 : list nat := Eval vm_compute in (BG.kept_list 48 PrzS.regs0 PrzS.regs_out1).
Lemma KS_rzS_1_ok : BG.kept_ok 48 PrzS.regs0 PrzS.regs_out1 KS_rzS_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma rzS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 11) = Z_to_bv 64 (V 37%nat) ->
  140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 -> aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 -> L5.u8_at RSEGS M (bv_unsigned (getr R (reg 10))) (V 33%nat) ->
  0 <= (V 33%nat) <= 44 -> Z.testbit (V 33%nat) 0 = false -> 0 <= (V 37%nat) <= 67125248 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x59000 M) (st fx' R' 0x59014 M')
        /\ (forall x, In x KS_rzS_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 33%nat) / 2)
        /\ (V 37%nat) <= ((V 33%nat) / 2))
      \/ (msteps RSEGS (st fx R 0x59000 M) (st fx' R' 0x58a84 M')
        /\ (forall x, In x KS_rzS_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 37%nat) - ((V 33%nat) / 2))
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 33%nat) / 2)
        /\ ((V 33%nat) / 2) < (V 37%nat))).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G11 pvzI4 K1 K2 K3 pvzI5 K5 pvzI6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K4l; move K4l before pvzI5; pose proof (proj2 pvzI5) as K4r; move K4r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K6l; move K6l before pvzI6; pose proof (proj2 pvzI6) as K6r; move K6r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PrzS.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PrzS.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PrzS.kn0).
  { unfold know_ok, PrzS.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K0l K0r) | evalEk ZA ltac:(clear) | clear - K0l K0r; lia | clear - K0l K0r; lia | clear - K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - K0l K0r) | evalEk ZA ltac:(clear - HV33l HV33r K4l K4r K5) | clear - K0l K0r; lia | clear - K0l K0r; lia | byte_tac ltac:(clear - HV33l HV33r K4l K4r K5) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K4l K4r K5) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K4l K4r K5) | clear; lia | rewrite (L5K.land1_bit0_false vz_33 ltac:(clear - HV33l HV33r K4l K4r K5; lia) K5); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PrzS.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PrzS.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PrzS.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PrzS.ps0) with 0x59014 in Hms. change (SR.ps_regs PrzS.ps0) with (map (fun i => (i, nth i PrzS.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PrzS.ps0) with PrzS.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PrzS.regs0 PrzS.regs_out0 48 KS_rzS_0 KS_rzS_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PrzS.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PrzS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PrzS.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PrzS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; cbn [In]; left; reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  - right.
    change (SR.ps_pc PrzS.ps1) with 0x58a84 in Hms. change (SR.ps_regs PrzS.ps1) with (map (fun i => (i, nth i PrzS.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PrzS.ps1) with PrzS.cells1 in Hcells. unfold PrzS.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PrzS.regs0 PrzS.regs_out1 48 KS_rzS_1 KS_rzS_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PrzS.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PrzS.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PrzS.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PrzS.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PrzS.regs_out1 E' R' 14 Hregs) by (clear; lia). cbn [nth PrzS.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; cbn [In]; left; reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PrzL := LibSegBs_rzL_u.
Definition KS_rzL_0 : list nat := Eval vm_compute in (BG.kept_list 48 PrzL.regs0 PrzL.regs_out0).
Lemma KS_rzL_0_ok : BG.kept_ok 48 PrzL.regs0 PrzL.regs_out0 KS_rzL_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_rzL_1 : list nat := Eval vm_compute in (BG.kept_list 48 PrzL.regs0 PrzL.regs_out1).
Lemma KS_rzL_1_ok : BG.kept_ok 48 PrzL.regs0 PrzL.regs_out1 KS_rzL_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma rzL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 11) = Z_to_bv 64 (V 37%nat) ->
  140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 -> aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 -> L5.u8_at RSEGS M (bv_unsigned (getr R (reg 10))) (V 33%nat) ->
  0 <= (V 33%nat) <= 255 -> Z.testbit (V 33%nat) 0 = true -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 34%nat) -> 0 <= (V 34%nat) <= 134217728 ->
  0 <= (V 37%nat) <= 67125248 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x59000 M) (st fx' R' 0x58a84 M')
        /\ (forall x, In x KS_rzL_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 (((-1) * (V 34%nat)) + (V 37%nat))
        /\ getr R' (reg 13) = Z_to_bv 64 1
        /\ getr R' (reg 14) = Z_to_bv 64 (V 34%nat)
        /\ (V 34%nat) < (V 37%nat))
      \/ (msteps RSEGS (st fx R 0x59000 M) (st fx' R' 0x59014 M')
        /\ (forall x, In x KS_rzL_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 13) = Z_to_bv 64 1
        /\ getr R' (reg 14) = Z_to_bv 64 (V 34%nat)
        /\ (V 37%nat) <= (V 34%nat))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G11 pvzI5 K1 K2 K3 pvzI6 K5 K6 pvzI7 pvzI8.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K4l; move K4l before pvzI6; pose proof (proj2 pvzI6) as K4r; move K4r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K7l; move K7l before pvzI7; pose proof (proj2 pvzI7) as K7r; move K7r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K8l; move K8l before pvzI8; pose proof (proj2 pvzI8) as K8r; move K8r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PrzL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PrzL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PrzL.kn0).
  { unfold know_ok, PrzL.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K0l K0r) | evalEk ZA ltac:(clear) | clear - K0l K0r; lia | clear - K0l K0r; lia | clear - K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - K0l K0r) | evalEk ZA ltac:(clear - HV33l HV33r K4l K4r K5) | clear - K0l K0r; lia | clear - K0l K0r; lia | byte_tac ltac:(clear - HV33l HV33r K4l K4r K5) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K4l K4r K5) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K4l K4r K5) | clear; lia | rewrite (L5K.land1_bit0_true vz_33 ltac:(clear - HV33l HV33r K4l K4r K5; lia) K5); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K0l K0r) | evalEk ZA ltac:(clear - HV34l HV34r K7l K7r) | clear - K0l K0r; lia | clear - K0l K0r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PrzL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PrzL.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PrzL.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PrzL.ps0) with 0x58a84 in Hms. change (SR.ps_regs PrzL.ps0) with (map (fun i => (i, nth i PrzL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PrzL.ps0) with PrzL.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PrzL.regs0 PrzL.regs_out0 48 KS_rzL_0 KS_rzL_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PrzL.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PrzL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PrzL.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PrzL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PrzL.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PrzL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; cbn [In]; left; reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  - right.
    change (SR.ps_pc PrzL.ps1) with 0x59014 in Hms. change (SR.ps_regs PrzL.ps1) with (map (fun i => (i, nth i PrzL.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PrzL.ps1) with PrzL.cells1 in Hcells. unfold PrzL.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PrzL.regs0 PrzL.regs_out1 48 KS_rzL_1 KS_rzL_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PrzL.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PrzL.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PrzL.regs_out1 E' R' 14 Hregs) by (clear; lia). cbn [nth PrzL.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; cbn [In]; left; reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PrzTS := LibSegBs_rzTS_u.
Definition KS_rzTS : list nat := Eval vm_compute in (BG.kept_list 48 PrzTS.regs0 PrzTS.regs_out0).
Lemma KS_rzTS_ok : BG.kept_ok 48 PrzTS.regs0 PrzTS.regs_out0 KS_rzTS = true. Proof. vm_compute. reflexivity. Qed.
Lemma rzTS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 11) = Z_to_bv 64 (V 37%nat) -> getr R (reg 13) = Z_to_bv 64 0 ->
  140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 -> aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 -> 0 <= (V 37%nat) <= 22 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((bv_unsigned (getr R (reg 10))) + 0) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((bv_unsigned (getr R (reg 10))) + 0) <= i < ((bv_unsigned (getr R (reg 10))) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x59014 M) (st fx' R' 0x5902c M')
        /\ (forall x, In x KS_rzTS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 (((bv_unsigned (getr R (reg 10))) + (V 37%nat)) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 ((bv_unsigned (getr R (reg 10))) + 1)
        /\ getr R' (reg 13) = Z_to_bv 64 (2 * (V 37%nat))
        /\ L5.u8_at RSEGS M' (((bv_unsigned (getr R (reg 10))) + (V 37%nat)) + 1) 0
        /\ L5.u8_at RSEGS M' (bv_unsigned (getr R (reg 10))) (2 * (V 37%nat))).
Proof.
  intros pvzI1 pvzI2 G2 G11 G13 pvzI3 K1 K2 pvzI4.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV37l; move HV37l before pvzI2; pose proof (proj2 pvzI2) as HV37r; move HV37r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as K0l; move K0l before pvzI3; pose proof (proj2 pvzI3) as K0r; move K0r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K3l; move K3l before pvzI4; pose proof (proj2 pvzI4) as K3r; move K3r before pvzI4; clear pvzI4.
  set (vz_2 := V 2%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PrzTS.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PrzTS.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PrzTS.kn0).
  { unfold know_ok, PrzTS.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K0l K0r) | evalEk ZA ltac:(clear) | clear - K0l K0r; lia | clear - K0l K0r; lia | clear - K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PrzTS.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PrzTS.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((bv_unsigned (getr R (reg 10))) + 0) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 0) + 24) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PrzTS.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PrzTS.ps0) with 0x5902c in Hms. change (SR.ps_regs PrzTS.ps0) with (map (fun i => (i, nth i PrzTS.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PrzTS.ps0) with PrzTS.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PrzTS.regs0 PrzTS.regs_out0 48 KS_rzTS KS_rzTS_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PrzTS.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PrzTS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzTS.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PrzTS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzTS.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PrzTS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - K0l K0r HV37l HV37r K3l K3r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - K0l K0r) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K3l K3r) | byte_tac ltac:(clear - HV37l HV37r K3l K3r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PrzTL := LibSegBs_rzTL_u.
Definition KS_rzTL : list nat := Eval vm_compute in (BG.kept_list 48 PrzTL.regs0 PrzTL.regs_out0).
Lemma KS_rzTL_ok : BG.kept_ok 48 PrzTL.regs0 PrzTL.regs_out0 KS_rzTL = true. Proof. vm_compute. reflexivity. Qed.
Lemma rzTL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 11) = Z_to_bv 64 (V 37%nat) -> getr R (reg 13) = Z_to_bv 64 1 ->
  140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 -> aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 -> 0 <= (V 37%nat) <= 134217728 ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 16) (V 35%nat) -> 4096 <= (V 35%nat) <= 140737488355328 -> L5.writable RSEGS M ((V 35%nat) + (V 37%nat)) 1 -> (((V 35%nat) + (V 37%nat)) + 1 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= ((V 35%nat) + (V 37%nat))) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((bv_unsigned (getr R (reg 10))) + 8) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 8) + 8) -> ~ ((((V 35%nat) + (V 37%nat)) + 0) <= bv_unsigned a < (((V 35%nat) + (V 37%nat)) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((bv_unsigned (getr R (reg 10))) + 8) <= i < ((bv_unsigned (getr R (reg 10))) + 8) + 8) -> ~ ((((V 35%nat) + (V 37%nat)) + 0) <= i < (((V 35%nat) + (V 37%nat)) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x59014 M) (st fx' R' 0x59050 M')
        /\ (forall x, In x KS_rzTL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 35%nat) + (V 37%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 (V 35%nat)
        /\ L5.u8_at RSEGS M' ((V 35%nat) + (V 37%nat)) 0
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 8) (V 37%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G11 G13 pvzI4 K1 K2 pvzI5 K4 pvzI6 K6 K7.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV35l; move HV35l before pvzI2; pose proof (proj2 pvzI2) as HV35r; move HV35r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K3l; move K3l before pvzI5; pose proof (proj2 pvzI5) as K3r; move K3r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K5l; move K5l before pvzI6; pose proof (proj2 pvzI6) as K5r; move K5r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 35%nat => vz_35 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PrzTL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PrzTL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PrzTL.kn0).
  { unfold know_ok, PrzTL.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K0l K0r K7) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K0l K0r K7) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K0l K0r K7) | evalEk ZA ltac:(clear) | clear - K0l K0r K7; lia | clear - K0l K0r K7; lia | clear - K0l K0r K7; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K3l K3r K7) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K0l K0r K7) | evalEk ZA ltac:(clear - HV35l HV35r K5l K5r K7) | clear - K0l K0r K7; lia | clear - K0l K0r K7; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K5l K5r K7) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV35l HV35r K5l K5r K7 HV37l HV37r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K5l K5r K7 HV37l HV37r K3l K3r; lia | clear - HV35l HV35r K5l K5r K7 HV37l HV37r K3l K3r; lia | clear - HV35l HV35r K5l K5r K7 HV37l HV37r K3l K3r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K5l K5r K7 HV37l HV37r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K0l K0r K7) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PrzTL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PrzTL.NX0 with 48%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((bv_unsigned (getr R (reg 10))) + 8) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 8) + 8) -> ~ (((vz_35 + vz_37) + 0) <= bv_unsigned a < ((vz_35 + vz_37) + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PrzTL.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear - K0l K0r K7 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV35l HV35r K5l K5r K7 HV37l HV37r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV35l HV35r K5l K5r K7 HV37l HV37r K3l K3r Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PrzTL.ps0) with 0x59050 in Hms. change (SR.ps_regs PrzTL.ps0) with (map (fun i => (i, nth i PrzTL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PrzTL.ps0) with PrzTL.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PrzTL.regs0 PrzTL.regs_out0 48 KS_rzTL KS_rzTL_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PrzTL.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PrzTL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrzTL.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PrzTL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV35l HV35r K5l K5r K7 HV37l HV37r K3l K3r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K3l K3r K7) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PapS0 := LibSegBs_apS0_u.
Definition KS_apS0_0 : list nat := Eval vm_compute in (BG.kept_list 60 PapS0.regs0 PapS0.regs_out0).
Lemma KS_apS0_0_ok : BG.kept_ok 60 PapS0.regs0 PapS0.regs_out0 KS_apS0_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_apS0_1 : list nat := Eval vm_compute in (BG.kept_list 60 PapS0.regs0 PapS0.regs_out1).
Lemma KS_apS0_1_ok : BG.kept_ok 60 PapS0.regs0 PapS0.regs_out1 KS_apS0_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma apS0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 11) = Z_to_bv 64 (V 43%nat) ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 -> (((V 2%nat) - 80) + 80 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= ((V 2%nat) - 80)) -> L5.u8_at RSEGS M (bv_unsigned (getr R (reg 10))) (V 33%nat) ->
  0 <= (V 33%nat) <= 44 -> Z.testbit (V 33%nat) 0 = false -> L5.u64_at RSEGS M (bv_unsigned (getr R (reg 10))) (V 36%nat) -> Z.testbit (V 36%nat) 0 = false ->
  0 <= (((72057594037927936 * (V 36%nat)) mod 2 ^ 64) / 144115188075855872) <= 22 -> 1 <= (V 43%nat) <= 67125248 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 80) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 80) <= i < ((V 2%nat) - 80) + 80) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x58a84 M) (st fx' R' 0x58ae8 M')
        /\ (forall x, In x KS_apS0_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ bv_unsigned (getr R' (reg 11)) = ((((18446744073709551615 * (((72057594037927936 * (V 36%nat)) mod 2 ^ 64) / 144115188075855872)) mod 2 ^ 64) + 22) mod 2 ^ 64)
        /\ bv_unsigned (getr R' (reg 18)) = (((72057594037927936 * (V 36%nat)) mod 2 ^ 64) / 144115188075855872)
        /\ getr R' (reg 23) = Z_to_bv 64 22
        /\ (V 43%nat) <= ((((18446744073709551615 * (((72057594037927936 * (V 36%nat)) mod 2 ^ 64) / 144115188075855872)) mod 2 ^ 64) + 22) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))
      \/ (msteps RSEGS (st fx R 0x58a84 M) (st fx' R' 0x58b10 M')
        /\ (forall x, In x KS_apS0_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ bv_unsigned (getr R' (reg 11)) = ((((18446744073709551615 * (((72057594037927936 * (V 36%nat)) mod 2 ^ 64) / 144115188075855872)) mod 2 ^ 64) + 22) mod 2 ^ 64)
        /\ bv_unsigned (getr R' (reg 18)) = (((72057594037927936 * (V 36%nat)) mod 2 ^ 64) / 144115188075855872)
        /\ getr R' (reg 23) = Z_to_bv 64 22
        /\ ((((18446744073709551615 * (((72057594037927936 * (V 36%nat)) mod 2 ^ 64) / 144115188075855872)) mod 2 ^ 64) + 22) mod 2 ^ 64) < (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G11 pvzI5 K1 K2 pvzI6 K4 K5 K6 K7 pvzI7 K9 K10 K11 K12 pvzI8.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV43l; move HV43l before pvzI4; pose proof (proj2 pvzI4) as HV43r; move HV43r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K8l; move K8l before pvzI7; pose proof (proj2 pvzI7) as K8r; move K8r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K13l; move K13l before pvzI8; pose proof (proj2 pvzI8) as K13r; move K13r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_43 := V 43%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 36%nat => Z_to_bv 64 vz_36 | 43%nat => Z_to_bv 64 vz_43 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 36%nat => vz_36 | 43%nat => vz_43 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E PapS0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapS0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapS0.kn0).
  { unfold know_ok, PapS0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K3l K3r K6) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K3l K3r K6) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K3l K3r K6) | evalEk ZA ltac:(clear) | clear - K3l K3r K6; lia | clear - K3l K3r K6; lia | clear - K3l K3r K6; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - K3l K3r K6) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K9) | clear - K3l K3r K6; lia | clear - K3l K3r K6; lia | byte_tac ltac:(clear - HV33l HV33r K8l K8r K9) | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K9) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K9) | clear; lia | rewrite (L5K.land1_bit0_false vz_33 ltac:(clear - HV33l HV33r K8l K8r K9; lia) K9); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6) | evalEk ZA ltac:(clear - HV36l HV36r K11) | clear - K3l K3r K6; lia | clear - K3l K3r K6; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV36l HV36r K11) | clear; lia | rewrite (L5K.land1_bit0_false vz_36 ltac:(clear - HV36l HV36r K11; lia) K11); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K13l K13r) | exact (conj K13l K13r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PapS0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapS0.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 80) <= bv_unsigned a < (vz_2 - 80) + 80) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PapS0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PapS0.ps0) with 0x58ae8 in Hms. change (SR.ps_regs PapS0.ps0) with (map (fun i => (i, nth i PapS0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PapS0.ps0) with PapS0.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PapS0.regs0 PapS0.regs_out0 60 KS_apS0_0 KS_apS0_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PapS0.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PapS0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PapS0.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PapS0.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PapS0.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PapS0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PapS0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PapS0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PapS0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PapS0.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PapS0.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PapS0.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PapS0.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PapS0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; cbn [In]; left; reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
  - right.
    change (SR.ps_pc PapS0.ps1) with 0x58b10 in Hms. change (SR.ps_regs PapS0.ps1) with (map (fun i => (i, nth i PapS0.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PapS0.ps1) with PapS0.cells1 in Hcells. unfold PapS0.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PapS0.regs0 PapS0.regs_out1 60 KS_apS0_1 KS_apS0_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PapS0.regs_out1 E' R' 2 Hregs) by (clear; lia). cbn [nth PapS0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PapS0.regs_out1 E' R' 8 Hregs) by (clear; lia). cbn [nth PapS0.regs_out1]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PapS0.regs_out1 E' R' 9 Hregs) by (clear; lia). cbn [nth PapS0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PapS0.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PapS0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PapS0.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PapS0.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PapS0.regs_out1 E' R' 18 Hregs) by (clear; lia). cbn [nth PapS0.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PapS0.regs_out1 E' R' 23 Hregs) by (clear; lia). cbn [nth PapS0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; cbn [In]; left; reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PapL0 := LibSegBs_apL0_u.
Definition KS_apL0_0 : list nat := Eval vm_compute in (BG.kept_list 60 PapL0.regs0 PapL0.regs_out0).
Lemma KS_apL0_0_ok : BG.kept_ok 60 PapL0.regs0 PapL0.regs_out0 KS_apL0_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_apL0_1 : list nat := Eval vm_compute in (BG.kept_list 60 PapL0.regs0 PapL0.regs_out1).
Lemma KS_apL0_1_ok : BG.kept_ok 60 PapL0.regs0 PapL0.regs_out1 KS_apL0_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma apL0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 11) = Z_to_bv 64 (V 43%nat) ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 -> (((V 2%nat) - 80) + 80 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= ((V 2%nat) - 80)) -> L5.u8_at RSEGS M (bv_unsigned (getr R (reg 10))) (V 33%nat) ->
  0 <= (V 33%nat) <= 255 -> Z.testbit (V 33%nat) 0 = true -> L5.u64_at RSEGS M (bv_unsigned (getr R (reg 10))) (V 36%nat) -> Z.testbit (V 36%nat) 0 = true ->
  27 <= (V 36%nat) <= 134217729 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 34%nat) -> 0 <= (V 34%nat) <= 134217728 -> 1 <= (V 43%nat) <= 67125248 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 80) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 80) <= i < ((V 2%nat) - 80) + 80) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x58a84 M) (st fx' R' 0x58ae8 M')
        /\ (forall x, In x KS_apL0_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 ((((-1) * (V 34%nat)) + (2 * ((V 36%nat) / 2))) - 1)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 ((2 * ((V 36%nat) / 2)) - 1)
        /\ (V 43%nat) <= ((((((18446744073709551615 * (V 34%nat)) mod 2 ^ 64) + ((2 * ((V 36%nat) / 2)) mod 2 ^ 64)) mod 2 ^ 64) + 18446744073709551615) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))
      \/ (msteps RSEGS (st fx R 0x58a84 M) (st fx' R' 0x58b10 M')
        /\ (forall x, In x KS_apL0_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 ((((-1) * (V 34%nat)) + (2 * ((V 36%nat) / 2))) - 1)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 ((2 * ((V 36%nat) / 2)) - 1)
        /\ ((((((18446744073709551615 * (V 34%nat)) mod 2 ^ 64) + ((2 * ((V 36%nat) / 2)) mod 2 ^ 64)) mod 2 ^ 64) + 18446744073709551615) mod 2 ^ 64) < (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G11 pvzI6 K1 K2 pvzI7 K4 K5 K6 K7 pvzI8 K9 K10 K11 pvzI9 K13 pvzI10 pvzI11.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV43l; move HV43l before pvzI5; pose proof (proj2 pvzI5) as HV43r; move HV43r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K8l; move K8l before pvzI8; pose proof (proj2 pvzI8) as K8r; move K8r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K12l; move K12l before pvzI9; pose proof (proj2 pvzI9) as K12r; move K12r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K14l; move K14l before pvzI10; pose proof (proj2 pvzI10) as K14r; move K14r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K15l; move K15l before pvzI11; pose proof (proj2 pvzI11) as K15r; move K15r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_43 := V 43%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 43%nat => Z_to_bv 64 vz_43 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 43%nat => vz_43 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E PapL0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapL0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapL0.kn0).
  { unfold know_ok, PapL0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K3l K3r K6) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K3l K3r K6) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K3l K3r K6) | evalEk ZA ltac:(clear) | clear - K3l K3r K6; lia | clear - K3l K3r K6; lia | clear - K3l K3r K6; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - K3l K3r K6) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K9) | clear - K3l K3r K6; lia | clear - K3l K3r K6; lia | byte_tac ltac:(clear - HV33l HV33r K8l K8r K9) | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K9) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K9) | clear; lia | rewrite (L5K.land1_bit0_true vz_33 ltac:(clear - HV33l HV33r K8l K8r K9; lia) K9); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6) | evalEk ZA ltac:(clear - HV36l HV36r K11 K12l K12r) | clear - K3l K3r K6; lia | clear - K3l K3r K6; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV36l HV36r K11 K12l K12r) | clear; lia | rewrite (L5K.land1_bit0_true vz_36 ltac:(clear - HV36l HV36r K11 K12l K12r; lia) K11); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K11 K12l K12r) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r) | clear - K3l K3r K6; lia | clear - K3l K3r K6; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K15l K15r) | exact (conj K15l K15r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PapL0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapL0.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 80) <= bv_unsigned a < (vz_2 - 80) + 80) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PapL0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PapL0.ps0) with 0x58ae8 in Hms. change (SR.ps_regs PapL0.ps0) with (map (fun i => (i, nth i PapL0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PapL0.ps0) with PapL0.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PapL0.regs0 PapL0.regs_out0 60 KS_apL0_0 KS_apL0_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PapL0.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PapL0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PapL0.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PapL0.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PapL0.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PapL0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PapL0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PapL0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PapL0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PapL0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PapL0.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PapL0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PapL0.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PapL0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; cbn [In]; left; reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
  - right.
    change (SR.ps_pc PapL0.ps1) with 0x58b10 in Hms. change (SR.ps_regs PapL0.ps1) with (map (fun i => (i, nth i PapL0.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PapL0.ps1) with PapL0.cells1 in Hcells. unfold PapL0.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PapL0.regs0 PapL0.regs_out1 60 KS_apL0_1 KS_apL0_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PapL0.regs_out1 E' R' 2 Hregs) by (clear; lia). cbn [nth PapL0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PapL0.regs_out1 E' R' 8 Hregs) by (clear; lia). cbn [nth PapL0.regs_out1]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PapL0.regs_out1 E' R' 9 Hregs) by (clear; lia). cbn [nth PapL0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PapL0.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PapL0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PapL0.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PapL0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PapL0.regs_out1 E' R' 18 Hregs) by (clear; lia). cbn [nth PapL0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PapL0.regs_out1 E' R' 23 Hregs) by (clear; lia). cbn [nth PapL0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; cbn [In]; left; reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; right; right; right; right; right; right; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PfitS := LibSegBs_fitS_u.
Definition KS_fitS : list nat := Eval vm_compute in (BG.kept_list 60 PfitS.regs0 PfitS.regs_out0).
Lemma KS_fitS_ok : BG.kept_ok 60 PfitS.regs0 PfitS.regs_out0 KS_fitS = true. Proof. vm_compute. reflexivity. Qed.
Lemma fitS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 43%nat) -> getr R (reg 10) = Z_to_bv 64 0 -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 22 ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 140735332483072 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 24 -> (((V 2%nat) - 80) + 80 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 80)) -> 0 <= (V 34%nat) <= 22 ->
  1 <= (V 43%nat) <= 22 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x58ae8 M) (st fx' R' 0xaba00 M')
        /\ (forall x, In x KS_fitS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 363520
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 10%nat) + (V 34%nat)) + 1)
        /\ getr R' (reg 11) = getr R (reg 12)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 10%nat) + 1)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 34%nat) + (V 43%nat))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G10 G18 G23 pvzI5 K1 K2 pvzI6 K4 K5 K6 pvzI7 pvzI8.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV43l; move HV43l before pvzI4; pose proof (proj2 pvzI4) as HV43r; move HV43r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K7l; move K7l before pvzI7; pose proof (proj2 pvzI7) as K7r; move K7r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K8l; move K8l before pvzI8; pose proof (proj2 pvzI8) as K8r; move K8r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_43 := V 43%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 34%nat => Z_to_bv 64 vz_34 | 43%nat => Z_to_bv 64 vz_43 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 34%nat => vz_34 | 43%nat => vz_43 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E PfitS.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PfitS.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PfitS.kn0).
  { unfold know_ok, PfitS.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PfitS.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PfitS.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PfitS.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PfitS.ps0) with 0xaba00 in Hms. change (SR.ps_regs PfitS.ps0) with (map (fun i => (i, nth i PfitS.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PfitS.ps0) with PfitS.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PfitS.regs0 PfitS.regs_out0 60 KS_fitS KS_fitS_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PfitS.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PfitS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PfitS.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PfitS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PfitS.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PfitS.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PfitS.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PfitS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PfitS.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PfitS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PfitS.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PfitS.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PfitL := LibSegBs_fitL_u.
Definition KS_fitL : list nat := Eval vm_compute in (BG.kept_list 60 PfitL.regs0 PfitL.regs_out0).
Lemma KS_fitL_ok : BG.kept_ok 60 PfitL.regs0 PfitL.regs_out0 KS_fitL = true. Proof. vm_compute. reflexivity. Qed.
Lemma fitL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 43%nat) -> getr R (reg 10) = Z_to_bv 64 1 -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 140735332483072 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 24 -> (((V 2%nat) - 80) + 80 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 80)) -> 0 <= (V 34%nat) <= 134217728 ->
  1 <= (V 43%nat) <= 67125248 -> L5.u64_at RSEGS M ((V 10%nat) + 16) (V 35%nat) -> 4096 <= (V 35%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x58ae8 M) (st fx' R' 0xaba00 M')
        /\ (forall x, In x KS_fitL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 363520
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 34%nat) + (V 35%nat))
        /\ getr R' (reg 11) = getr R (reg 12)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 34%nat) + (V 43%nat))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G18 pvzI6 K1 K2 pvzI7 K4 K5 K6 pvzI8 pvzI9 K9 pvzI10.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV43l; move HV43l before pvzI5; pose proof (proj2 pvzI5) as HV43r; move HV43r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K7l; move K7l before pvzI8; pose proof (proj2 pvzI8) as K7r; move K7r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K8l; move K8l before pvzI9; pose proof (proj2 pvzI9) as K8r; move K8r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K10l; move K10l before pvzI10; pose proof (proj2 pvzI10) as K10r; move K10r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_43 := V 43%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 43%nat => Z_to_bv 64 vz_43 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 34%nat => vz_34 | 35%nat => vz_35 | 43%nat => vz_43 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E PfitL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PfitL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PfitL.kn0).
  { unfold know_ok, PfitL.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear - HV35l HV35r K10l K10r) | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PfitL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PfitL.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PfitL.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PfitL.ps0) with 0xaba00 in Hms. change (SR.ps_regs PfitL.ps0) with (map (fun i => (i, nth i PfitL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PfitL.ps0) with PfitL.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PfitL.regs0 PfitL.regs_out0 60 KS_fitL KS_fitL_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PfitL.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PfitL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PfitL.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PfitL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PfitL.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PfitL.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PfitL.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PfitL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PfitL.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PfitL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PfitL.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PfitL.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PapMS := LibSegBs_apMS_u.
Definition KS_apMS : list nat := Eval vm_compute in (BG.kept_list 60 PapMS.regs0 PapMS.regs_out0).
Lemma KS_apMS_ok : BG.kept_ok 60 PapMS.regs0 PapMS.regs_out0 KS_apMS = true. Proof. vm_compute. reflexivity. Qed.
Lemma apMS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 54%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 10%nat) + 1) -> getr R (reg 22) = Z_to_bv 64 (V 38%nat) ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 140735332483072 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 24 -> (((V 2%nat) - 80) + 80 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 80)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 52%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (V 53%nat) -> L5.u8_at RSEGS M (V 10%nat) (V 33%nat) -> 0 <= (V 33%nat) <= 255 -> Z.testbit (V 33%nat) 0 = false ->
  1 <= (V 38%nat) <= 22 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 10%nat) + 0) <= bv_unsigned a < ((V 10%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 10%nat) + 0) <= i < ((V 10%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x58c00 M) (st fx' R' 0x58c54 M')
        /\ (forall x, In x KS_apMS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 10%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 53%nat)
        /\ L5.u8_at RSEGS M' (((V 10%nat) + (V 38%nat)) + 1) 0
        /\ L5.u8_at RSEGS M' (V 10%nat) (2 * (V 38%nat))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 G2 G8 G10 G20 G22 pvzI16 K1 K2 pvzI17 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 pvzI18 K19 pvzI19.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV44l; move HV44l before pvzI5; pose proof (proj2 pvzI5) as HV44r; move HV44r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV45l; move HV45l before pvzI6; pose proof (proj2 pvzI6) as HV45r; move HV45r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV46l; move HV46l before pvzI7; pose proof (proj2 pvzI7) as HV46r; move HV46r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV47l; move HV47l before pvzI8; pose proof (proj2 pvzI8) as HV47r; move HV47r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV48l; move HV48l before pvzI9; pose proof (proj2 pvzI9) as HV48r; move HV48r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV49l; move HV49l before pvzI10; pose proof (proj2 pvzI10) as HV49r; move HV49r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV50l; move HV50l before pvzI11; pose proof (proj2 pvzI11) as HV50r; move HV50r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV51l; move HV51l before pvzI12; pose proof (proj2 pvzI12) as HV51r; move HV51r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV52l; move HV52l before pvzI13; pose proof (proj2 pvzI13) as HV52r; move HV52r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV53l; move HV53l before pvzI14; pose proof (proj2 pvzI14) as HV53r; move HV53r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV54l; move HV54l before pvzI15; pose proof (proj2 pvzI15) as HV54r; move HV54r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K0l; move K0l before pvzI16; pose proof (proj2 pvzI16) as K0r; move K0r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K3l; move K3l before pvzI17; pose proof (proj2 pvzI17) as K3r; move K3r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K18l; move K18l before pvzI18; pose proof (proj2 pvzI18) as K18r; move K18r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K20l; move K20l before pvzI19; pose proof (proj2 pvzI19) as K20r; move K20r before pvzI19; clear pvzI19.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *. set (vz_54 := V 54%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 33%nat => Z_to_bv 64 vz_33 | 38%nat => Z_to_bv 64 vz_38 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | 54%nat => Z_to_bv 64 vz_54 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 33%nat => vz_33 | 38%nat => vz_38 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | 53%nat => vz_53 | 54%nat => vz_54 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 55%nat. }
  assert (HR: regs_ok E PapMS.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapMS.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapMS.kn0).
  { unfold know_ok, PapMS.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear - HV33l HV33r K18l K18r K19) | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | byte_tac ltac:(clear - HV33l HV33r K18l K18r K19) | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K18l K18r K19) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K18l K18r K19) | clear; lia | rewrite (L5K.land1_bit0_false vz_33 ltac:(clear - HV33l HV33r K18l K18r K19; lia) K19); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PapMS.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapMS.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_10 + 0) <= bv_unsigned a < (vz_10 + 0) + 24) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PapMS.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk' ZA Hag ltac:(clear) | clear - HV10l HV10r K3l K3r K6 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PapMS.ps0) with 0x58c54 in Hms. change (SR.ps_regs PapMS.ps0) with (map (fun i => (i, nth i PapMS.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PapMS.ps0) with PapMS.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PapMS.regs0 PapMS.regs_out0 60 KS_apMS KS_apMS_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PapMS.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PapMS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapMS.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PapMS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapMS.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PapMS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapMS.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PapMS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapMS.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PapMS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapMS.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PapMS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapMS.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PapMS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapMS.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PapMS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapMS.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PapMS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapMS.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PapMS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapMS.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PapMS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapMS.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PapMS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6 HV38l HV38r K20l K20r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk' ZA Hag ltac:(clear - HV38l HV38r K20l K20r) | byte_tac ltac:(clear - HV38l HV38r K20l K20r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PapML := LibSegBs_apML_u.
Definition KS_apML : list nat := Eval vm_compute in (BG.kept_list 60 PapML.regs0 PapML.regs_out0).
Lemma KS_apML_ok : BG.kept_ok 60 PapML.regs0 PapML.regs_out0 KS_apML = true. Proof. vm_compute. reflexivity. Qed.
Lemma apML_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 54%nat) -> getr R (reg 20) = Z_to_bv 64 (V 35%nat) -> getr R (reg 22) = Z_to_bv 64 (V 38%nat) ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 140735332483072 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 24 -> (((V 2%nat) - 80) + 80 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 80)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 52%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (V 53%nat) -> L5.u8_at RSEGS M (V 10%nat) (V 33%nat) -> 0 <= (V 33%nat) <= 255 -> Z.testbit (V 33%nat) 0 = true ->
  1 <= (V 38%nat) <= 67125248 -> 4096 <= (V 35%nat) <= 140737488355328 -> L5.writable RSEGS M ((V 35%nat) + (V 38%nat)) 1 -> (((V 35%nat) + (V 38%nat)) + 1 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 35%nat) + (V 38%nat))) ->
  (((V 35%nat) + (V 38%nat)) + 1 <= ((V 2%nat) - 80) \/ ((V 2%nat) - 80) + 80 <= ((V 35%nat) + (V 38%nat))) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 10%nat) + 8) <= bv_unsigned a < ((V 10%nat) + 8) + 8) -> ~ ((((V 35%nat) + (V 38%nat)) + 0) <= bv_unsigned a < (((V 35%nat) + (V 38%nat)) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 10%nat) + 8) <= i < ((V 10%nat) + 8) + 8) -> ~ ((((V 35%nat) + (V 38%nat)) + 0) <= i < (((V 35%nat) + (V 38%nat)) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x58c00 M) (st fx' R' 0x58c54 M')
        /\ (forall x, In x KS_apML -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 10%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 53%nat)
        /\ L5.u8_at RSEGS M' ((V 35%nat) + (V 38%nat)) 0
        /\ L5.u64_at RSEGS M' ((V 10%nat) + 8) (V 38%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 G2 G8 G10 G20 G22 pvzI17 K1 K2 pvzI18 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 pvzI19 K19 pvzI20 pvzI21 K22 K23 K24.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV44l; move HV44l before pvzI6; pose proof (proj2 pvzI6) as HV44r; move HV44r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV45l; move HV45l before pvzI7; pose proof (proj2 pvzI7) as HV45r; move HV45r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV46l; move HV46l before pvzI8; pose proof (proj2 pvzI8) as HV46r; move HV46r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV47l; move HV47l before pvzI9; pose proof (proj2 pvzI9) as HV47r; move HV47r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV48l; move HV48l before pvzI10; pose proof (proj2 pvzI10) as HV48r; move HV48r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV49l; move HV49l before pvzI11; pose proof (proj2 pvzI11) as HV49r; move HV49r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV50l; move HV50l before pvzI12; pose proof (proj2 pvzI12) as HV50r; move HV50r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV51l; move HV51l before pvzI13; pose proof (proj2 pvzI13) as HV51r; move HV51r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV52l; move HV52l before pvzI14; pose proof (proj2 pvzI14) as HV52r; move HV52r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV53l; move HV53l before pvzI15; pose proof (proj2 pvzI15) as HV53r; move HV53r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV54l; move HV54l before pvzI16; pose proof (proj2 pvzI16) as HV54r; move HV54r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K0l; move K0l before pvzI17; pose proof (proj2 pvzI17) as K0r; move K0r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K3l; move K3l before pvzI18; pose proof (proj2 pvzI18) as K3r; move K3r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K18l; move K18l before pvzI19; pose proof (proj2 pvzI19) as K18r; move K18r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K20l; move K20l before pvzI20; pose proof (proj2 pvzI20) as K20r; move K20r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K21l; move K21l before pvzI21; pose proof (proj2 pvzI21) as K21r; move K21r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *. set (vz_54 := V 54%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 38%nat => Z_to_bv 64 vz_38 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | 54%nat => Z_to_bv 64 vz_54 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 33%nat => vz_33 | 35%nat => vz_35 | 38%nat => vz_38 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | 53%nat => vz_53 | 54%nat => vz_54 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 55%nat. }
  assert (HR: regs_ok E PapML.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapML.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapML.kn0).
  { unfold know_ok, PapML.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K24; lia | clear - HV2l HV2r K0l K0r K6 K24; lia | clear - HV2l HV2r K0l K0r K6 K24; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K23) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K23) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K23) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K3l K3r K6 K23; lia | clear - HV10l HV10r K3l K3r K6 K23; lia | clear - HV10l HV10r K3l K3r K6 K23; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K23) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K6 K24; lia | clear - HV2l HV2r K0l K0r K6 K24; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K6 K24; lia | clear - HV2l HV2r K0l K0r K6 K24; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K6 K24; lia | clear - HV2l HV2r K0l K0r K6 K24; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K6 K24; lia | clear - HV2l HV2r K0l K0r K6 K24; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K6 K24; lia | clear - HV2l HV2r K0l K0r K6 K24; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K6 K24; lia | clear - HV2l HV2r K0l K0r K6 K24; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K6 K24; lia | clear - HV2l HV2r K0l K0r K6 K24; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r K6 K24; lia | clear - HV2l HV2r K0l K0r K6 K24; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K0l K0r K6 K24; lia | clear - HV2l HV2r K0l K0r K6 K24; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K0l K0r K6 K24; lia | clear - HV2l HV2r K0l K0r K6 K24; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K23) | evalEk ZA ltac:(clear - HV33l HV33r K18l K18r K19) | clear - HV10l HV10r K3l K3r K6 K23; lia | clear - HV10l HV10r K3l K3r K6 K23; lia | byte_tac ltac:(clear - HV33l HV33r K18l K18r K19) | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K18l K18r K19) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV33l HV33r K18l K18r K19) | clear; lia | rewrite (L5K.land1_bit0_true vz_33 ltac:(clear - HV33l HV33r K18l K18r K19; lia) K19); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K20l K20r K23 K24) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K21l K21r K23 K24) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV35l HV35r K21l K21r K23 K24 HV38l HV38r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K21l K21r K23 K24 HV38l HV38r K20l K20r; lia | clear - HV35l HV35r K21l K21r K23 K24 HV38l HV38r K20l K20r; lia | clear - HV35l HV35r K21l K21r K23 K24 HV38l HV38r K20l K20r; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K21l K21r K23 K24 HV38l HV38r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K23) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K21l K21r K23 K24 HV38l HV38r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K24) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PapML.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapML.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_10 + 8) <= bv_unsigned a < (vz_10 + 8) + 8) -> ~ (((vz_35 + vz_38) + 0) <= bv_unsigned a < ((vz_35 + vz_38) + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PapML.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6 K23) | evalEk' ZA Hag ltac:(clear) | clear - HV10l HV10r K3l K3r K6 K23 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV35l HV35r K21l K21r K23 K24 HV38l HV38r K20l K20r) | evalEk' ZA Hag ltac:(clear) | clear - HV35l HV35r K21l K21r K23 K24 HV38l HV38r K20l K20r Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PapML.ps0) with 0x58c54 in Hms. change (SR.ps_regs PapML.ps0) with (map (fun i => (i, nth i PapML.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PapML.ps0) with PapML.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PapML.regs0 PapML.regs_out0 60 KS_apML KS_apML_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PapML.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PapML.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapML.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PapML.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapML.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PapML.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapML.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PapML.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapML.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PapML.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapML.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PapML.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapML.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PapML.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapML.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PapML.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapML.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PapML.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapML.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PapML.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapML.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PapML.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapML.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PapML.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV35l HV35r K21l K21r K23 K24 HV38l HV38r K20l K20r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6 K23) | evalEk' ZA Hag ltac:(clear - HV38l HV38r K20l K20r K23 K24) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PgrowS := LibSegBs_growS_u.
Definition KS_growS_0 : list nat := Eval vm_compute in (BG.kept_list 60 PgrowS.regs0 PgrowS.regs_out0).
Lemma KS_growS_0_ok : BG.kept_ok 60 PgrowS.regs0 PgrowS.regs_out0 KS_growS_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_growS_1 : list nat := Eval vm_compute in (BG.kept_list 60 PgrowS.regs0 PgrowS.regs_out1).
Lemma KS_growS_1_ok : BG.kept_ok 60 PgrowS.regs0 PgrowS.regs_out1 KS_growS_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma growS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 43%nat) -> getr R (reg 10) = Z_to_bv 64 0 -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 22 ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 140735332483072 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 24 -> (((V 2%nat) - 80) + 80 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 80)) -> 0 <= (V 34%nat) <= 22 ->
  1 <= (V 43%nat) <= 67125248 -> 1 <= (((V 34%nat) + (V 43%nat)) - 22) <= 67125248 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x58b10 M) (st fx' R' 0x58b88 M')
        /\ (forall x, In x KS_growS_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 34%nat) + (V 43%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 23
        /\ getr R' (reg 13) = Z_to_bv 64 (((V 34%nat) + (V 43%nat)) - 22)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 10%nat) + 1)
        /\ getr R' (reg 21) = Z_to_bv 64 ((8 * (((V 34%nat) + (V 43%nat)) / 8)) + 7)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 34%nat) + (V 43%nat))
        /\ 44 < (((V 34%nat) + (V 43%nat)) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x58b10 M) (st fx' R' 0xb03b8 M')
        /\ (forall x, In x KS_growS_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 363440
        /\ getr R' (reg 10) = Z_to_bv 64 48
        /\ getr R' (reg 11) = Z_to_bv 64 23
        /\ getr R' (reg 13) = Z_to_bv 64 (((V 34%nat) + (V 43%nat)) - 22)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 10%nat) + 1)
        /\ getr R' (reg 21) = Z_to_bv 64 48
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 34%nat) + (V 43%nat))
        /\ getr R' (reg 24) = getr R (reg 12)
        /\ (((V 34%nat) + (V 43%nat)) mod 2 ^ 64) <= 44)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G10 G18 G23 pvzI5 K1 K2 pvzI6 K4 K5 K6 pvzI7 pvzI8 pvzI9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV43l; move HV43l before pvzI4; pose proof (proj2 pvzI4) as HV43r; move HV43r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K7l; move K7l before pvzI7; pose proof (proj2 pvzI7) as K7r; move K7r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K8l; move K8l before pvzI8; pose proof (proj2 pvzI8) as K8r; move K8r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K9l; move K9l before pvzI9; pose proof (proj2 pvzI9) as K9r; move K9r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_43 := V 43%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 34%nat => Z_to_bv 64 vz_34 | 43%nat => Z_to_bv 64 vz_43 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 34%nat => vz_34 | 43%nat => vz_43 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E PgrowS.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PgrowS.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PgrowS.kn0).
  { unfold know_ok, PgrowS.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K7l K7r K9l K9r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K8l K8r K9l K9r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K7l K7r K9l K9r HV43l HV43r K8l K8r) | exact (conj K9l K9r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PgrowS.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PgrowS.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PgrowS.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PgrowS.ps0) with 0x58b88 in Hms. change (SR.ps_regs PgrowS.ps0) with (map (fun i => (i, nth i PgrowS.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PgrowS.ps0) with PgrowS.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PgrowS.regs0 PgrowS.regs_out0 60 KS_growS_0 KS_growS_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PgrowS.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PgrowS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PgrowS.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PgrowS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PgrowS.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PgrowS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PgrowS.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PgrowS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PgrowS.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PgrowS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PgrowS.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PgrowS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; cbn [In]; left; reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  - right.
    change (SR.ps_pc PgrowS.ps1) with 0xb03b8 in Hms. change (SR.ps_regs PgrowS.ps1) with (map (fun i => (i, nth i PgrowS.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PgrowS.ps1) with PgrowS.cells1 in Hcells. unfold PgrowS.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PgrowS.regs0 PgrowS.regs_out1 60 KS_growS_1 KS_growS_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PgrowS.regs_out1 E' R' 1 Hregs) by (clear; lia). cbn [nth PgrowS.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PgrowS.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PgrowS.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PgrowS.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PgrowS.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PgrowS.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PgrowS.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PgrowS.regs_out1 E' R' 19 Hregs) by (clear; lia). cbn [nth PgrowS.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PgrowS.regs_out1 E' R' 21 Hregs) by (clear; lia). cbn [nth PgrowS.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PgrowS.regs_out1 E' R' 22 Hregs) by (clear; lia). cbn [nth PgrowS.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PgrowS.regs_out1 E' R' 24 Hregs) by (clear; lia). cbn [nth PgrowS.regs_out1]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; cbn [In]; left; reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PgrowL := LibSegBs_growL_u.
Definition KS_growL_0 : list nat := Eval vm_compute in (BG.kept_list 60 PgrowL.regs0 PgrowL.regs_out0).
Lemma KS_growL_0_ok : BG.kept_ok 60 PgrowL.regs0 PgrowL.regs_out0 KS_growL_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_growL_1 : list nat := Eval vm_compute in (BG.kept_list 60 PgrowL.regs0 PgrowL.regs_out1).
Lemma KS_growL_1_ok : BG.kept_ok 60 PgrowL.regs0 PgrowL.regs_out1 KS_growL_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma growL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 43%nat) -> getr R (reg 10) = Z_to_bv 64 1 -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 (V 37%nat) ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 140735332483072 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 24 -> (((V 2%nat) - 80) + 80 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 80)) -> 0 <= (V 34%nat) <= 134217728 ->
  1 <= (V 43%nat) <= 67125248 -> 25 <= (V 37%nat) <= 134217728 -> 1 <= ((V 34%nat) + (((-1) * (V 37%nat)) + (V 43%nat))) <= 67125248 -> L5.u64_at RSEGS M ((V 10%nat) + 16) (V 35%nat) ->
  4096 <= (V 35%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x58b10 M) (st fx' R' 0x58b88 M')
        /\ (forall x, In x KS_growL_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 34%nat) + (V 43%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 23
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 34%nat) + (((-1) * (V 37%nat)) + (V 43%nat)))
        /\ getr R' (reg 19) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 ((8 * (((V 34%nat) + (V 43%nat)) / 8)) + 7)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 34%nat) + (V 43%nat))
        /\ ((2 * (V 37%nat)) mod 2 ^ 64) < (((V 34%nat) + (V 43%nat)) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x58b10 M) (st fx' R' 0xb03b8 M')
        /\ (forall x, In x KS_growL_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 363440
        /\ getr R' (reg 10) = Z_to_bv 64 ((8 * ((2 * (V 37%nat)) / 8)) + 8)
        /\ getr R' (reg 11) = Z_to_bv 64 23
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 34%nat) + (((-1) * (V 37%nat)) + (V 43%nat)))
        /\ getr R' (reg 19) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 ((8 * ((2 * (V 37%nat)) / 8)) + 8)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 34%nat) + (V 43%nat))
        /\ getr R' (reg 24) = getr R (reg 12)
        /\ (((V 34%nat) + (V 43%nat)) mod 2 ^ 64) <= ((2 * (V 37%nat)) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G10 G18 G23 pvzI7 K1 K2 pvzI8 K4 K5 K6 pvzI9 pvzI10 pvzI11 pvzI12 K11 pvzI13.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV43l; move HV43l before pvzI6; pose proof (proj2 pvzI6) as HV43r; move HV43r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K7l; move K7l before pvzI9; pose proof (proj2 pvzI9) as K7r; move K7r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K8l; move K8l before pvzI10; pose proof (proj2 pvzI10) as K8r; move K8r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K9l; move K9l before pvzI11; pose proof (proj2 pvzI11) as K9r; move K9r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K10l; move K10l before pvzI12; pose proof (proj2 pvzI12) as K10r; move K10r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K12l; move K12l before pvzI13; pose proof (proj2 pvzI13) as K12r; move K12r before pvzI13; clear pvzI13.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_43 := V 43%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | 43%nat => Z_to_bv 64 vz_43 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 34%nat => vz_34 | 35%nat => vz_35 | 37%nat => vz_37 | 43%nat => vz_43 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E PgrowL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PgrowL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PgrowL.kn0).
  { unfold know_ok, PgrowL.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K7l K7r K10l K10r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K8l K8r K10l K10r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K9l K9r K10l K10r) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K7l K7r K10l K10r HV37l HV37r K9l K9r HV43l HV43r K8l K8r) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear - HV35l HV35r K12l K12r) | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K12l K12r) | exact (conj K12l K12r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PgrowL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PgrowL.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PgrowL.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PgrowL.ps0) with 0x58b88 in Hms. change (SR.ps_regs PgrowL.ps0) with (map (fun i => (i, nth i PgrowL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PgrowL.ps0) with PgrowL.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PgrowL.regs0 PgrowL.regs_out0 60 KS_growL_0 KS_growL_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PgrowL.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PgrowL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PgrowL.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PgrowL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PgrowL.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PgrowL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PgrowL.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PgrowL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PgrowL.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PgrowL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PgrowL.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PgrowL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; cbn [In]; left; reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  - right.
    change (SR.ps_pc PgrowL.ps1) with 0xb03b8 in Hms. change (SR.ps_regs PgrowL.ps1) with (map (fun i => (i, nth i PgrowL.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PgrowL.ps1) with PgrowL.cells1 in Hcells. unfold PgrowL.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PgrowL.regs0 PgrowL.regs_out1 60 KS_growL_1 KS_growL_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PgrowL.regs_out1 E' R' 1 Hregs) by (clear; lia). cbn [nth PgrowL.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PgrowL.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PgrowL.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PgrowL.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PgrowL.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PgrowL.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PgrowL.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PgrowL.regs_out1 E' R' 19 Hregs) by (clear; lia). cbn [nth PgrowL.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PgrowL.regs_out1 E' R' 21 Hregs) by (clear; lia). cbn [nth PgrowL.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PgrowL.regs_out1 E' R' 22 Hregs) by (clear; lia). cbn [nth PgrowL.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PgrowL.regs_out1 E' R' 24 Hregs) by (clear; lia). cbn [nth PgrowL.regs_out1]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; cbn [In]; left; reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Prec := LibSegBs_rec_u.
Definition KS_rec : list nat := Eval vm_compute in (BG.kept_list 60 Prec.regs0 Prec.regs_out0).
Lemma KS_rec_ok : BG.kept_ok 60 Prec.regs0 Prec.regs_out0 KS_rec = true. Proof. vm_compute. reflexivity. Qed.
Lemma rec_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 10) = Z_to_bv 64 (V 39%nat) -> getr R (reg 11) = Z_to_bv 64 23 -> getr R (reg 21) = Z_to_bv 64 (V 40%nat) ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 45 <= (V 39%nat) <= 268435456 ->
  47 <= (V 40%nat) <= 268435456 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x58b88 M) (st fx' R' 0xb03b8 M')
        /\ (forall x, In x KS_rec -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 363440
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 40%nat) + 1)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 40%nat) + 1)
        /\ getr R' (reg 24) = getr R (reg 12)).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G10 G11 G21 pvzI4 K1 K2 pvzI5 pvzI6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV39l; move HV39l before pvzI2; pose proof (proj2 pvzI2) as HV39r; move HV39r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV40l; move HV40l before pvzI3; pose proof (proj2 pvzI3) as HV40r; move HV40r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K3l; move K3l before pvzI5; pose proof (proj2 pvzI5) as K3r; move K3r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K4l; move K4l before pvzI6; pose proof (proj2 pvzI6) as K4r; move K4r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 39%nat => vz_39 | 40%nat => vz_40 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 41%nat. }
  assert (HR: regs_ok E Prec.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Prec.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Prec.kn0).
  { unfold know_ok, Prec.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Prec.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Prec.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Prec.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Prec.ps0) with 0xb03b8 in Hms. change (SR.ps_regs Prec.ps0) with (map (fun i => (i, nth i Prec.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Prec.ps0) with Prec.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Prec.regs0 Prec.regs_out0 60 KS_rec KS_rec_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Prec.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Prec.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Prec.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Prec.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Prec.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Prec.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Prec.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Prec.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PpN := LibSegBs_pN_u.
Definition KS_pN_0 : list nat := Eval vm_compute in (BG.kept_list 60 PpN.regs0 PpN.regs_out0).
Lemma KS_pN_0_ok : BG.kept_ok 60 PpN.regs0 PpN.regs_out0 KS_pN_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_pN_1 : list nat := Eval vm_compute in (BG.kept_list 60 PpN.regs0 PpN.regs_out1).
Lemma KS_pN_1_ok : BG.kept_ok 60 PpN.regs0 PpN.regs_out1 KS_pN_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma pN_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 10) = Z_to_bv 64 (V 41%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 (V 42%nat) ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 0 <= (V 34%nat) <= 134217728 ->
  4096 <= (V 41%nat) <= 140737488355328 -> 4096 <= (V 42%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x58bb0 M) (st fx' R' 0xab884 M')
        /\ (forall x, In x KS_pN_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 363464
        /\ getr R' (reg 11) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 41%nat)
        /\ 1 <= (((V 34%nat) - 0) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x58bb0 M) (st fx' R' 0x58bc8 M')
        /\ (forall x, In x KS_pN_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 20) = Z_to_bv 64 (V 41%nat)
        /\ (((V 34%nat) - 0) mod 2 ^ 64) < 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G10 G18 G19 pvzI5 K1 K2 pvzI6 pvzI7 pvzI8.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV34l; move HV34l before pvzI2; pose proof (proj2 pvzI2) as HV34r; move HV34r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV41l; move HV41l before pvzI3; pose proof (proj2 pvzI3) as HV41r; move HV41r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV42l; move HV42l before pvzI4; pose proof (proj2 pvzI4) as HV42r; move HV42r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K4l; move K4l before pvzI7; pose proof (proj2 pvzI7) as K4r; move K4r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K5l; move K5l before pvzI8; pose proof (proj2 pvzI8) as K5r; move K5r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 34%nat => Z_to_bv 64 vz_34 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 34%nat => vz_34 | 41%nat => vz_41 | 42%nat => vz_42 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 43%nat. }
  assert (HR: regs_ok E PpN.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PpN.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PpN.kn0).
  { unfold know_ok, PpN.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K5l K5r) | exact (conj K5l K5r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PpN.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PpN.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PpN.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PpN.ps0) with 0xab884 in Hms. change (SR.ps_regs PpN.ps0) with (map (fun i => (i, nth i PpN.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PpN.ps0) with PpN.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PpN.regs0 PpN.regs_out0 60 KS_pN_0 KS_pN_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PpN.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PpN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PpN.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PpN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PpN.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PpN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PpN.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PpN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; cbn [In]; left; reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  - right.
    change (SR.ps_pc PpN.ps1) with 0x58bc8 in Hms. change (SR.ps_regs PpN.ps1) with (map (fun i => (i, nth i PpN.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PpN.ps1) with PpN.cells1 in Hcells. unfold PpN.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PpN.regs0 PpN.regs_out1 60 KS_pN_1 KS_pN_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PpN.regs_out1 E' R' 20 Hregs) by (clear; lia). cbn [nth PpN.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; cbn [In]; left; reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PpDS := LibSegBs_pDS_u.
Definition KS_pDS : list nat := Eval vm_compute in (BG.kept_list 60 PpDS.regs0 PpDS.regs_out0).
Lemma KS_pDS_ok : BG.kept_ok 60 PpDS.regs0 PpDS.regs_out0 KS_pDS = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma pDS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 43%nat) -> getr R (reg 10) = Z_to_bv 64 (V 41%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 20) = Z_to_bv 64 (V 41%nat) -> getr R (reg 21) = Z_to_bv 64 (V 40%nat) -> getr R (reg 22) = Z_to_bv 64 (V 38%nat) -> getr R (reg 23) = Z_to_bv 64 22 -> getr R (reg 24) = Z_to_bv 64 (V 56%nat) ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 140735332483072 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 24 -> (((V 2%nat) - 80) + 80 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 80)) -> 0 <= (V 34%nat) <= 22 ->
  4096 <= (V 41%nat) <= 140737488355328 -> 48 <= (V 40%nat) <= 134217728 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 10%nat) + 0) <= bv_unsigned a < ((V 10%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 10%nat) + 0) <= i < ((V 10%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x58bc8 M) (st fx' R' 0xaba00 M')
        /\ (forall x, In x KS_pDS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 363520
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 34%nat) + (V 41%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 56%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 10%nat) + 16) (V 41%nat)
        /\ L5.u64_at RSEGS M' ((V 10%nat) + 8) (V 34%nat)
        /\ L5.u64_at RSEGS M' (V 10%nat) ((2 * ((V 40%nat) / 2)) + 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G10 G18 G20 G21 G22 G23 G24 pvzI9 K1 K2 pvzI10 K4 K5 K6 pvzI11 pvzI12 pvzI13.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV40l; move HV40l before pvzI5; pose proof (proj2 pvzI5) as HV40r; move HV40r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV41l; move HV41l before pvzI6; pose proof (proj2 pvzI6) as HV41r; move HV41r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV43l; move HV43l before pvzI7; pose proof (proj2 pvzI7) as HV43r; move HV43r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV56l; move HV56l before pvzI8; pose proof (proj2 pvzI8) as HV56r; move HV56r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K0l; move K0l before pvzI9; pose proof (proj2 pvzI9) as K0r; move K0r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K7l; move K7l before pvzI11; pose proof (proj2 pvzI11) as K7r; move K7r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K8l; move K8l before pvzI12; pose proof (proj2 pvzI12) as K8r; move K8r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K9l; move K9l before pvzI13; pose proof (proj2 pvzI13) as K9r; move K9r before pvzI13; clear pvzI13.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_56 := V 56%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 34%nat => Z_to_bv 64 vz_34 | 38%nat => Z_to_bv 64 vz_38 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 43%nat => Z_to_bv 64 vz_43 | 56%nat => Z_to_bv 64 vz_56 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 34%nat => vz_34 | 38%nat => vz_38 | 40%nat => vz_40 | 41%nat => vz_41 | 43%nat => vz_43 | 56%nat => vz_56 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 57%nat. }
  assert (HR: regs_ok E PpDS.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PpDS.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PpDS.kn0).
  { unfold know_ok, PpDS.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PpDS.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PpDS.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_10 + 0) <= bv_unsigned a < (vz_10 + 0) + 24) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PpDS.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk' ZA Hag ltac:(clear) | clear - HV10l HV10r K3l K3r K6 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PpDS.ps0) with 0xaba00 in Hms. change (SR.ps_regs PpDS.ps0) with (map (fun i => (i, nth i PpDS.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PpDS.ps0) with PpDS.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PpDS.regs0 PpDS.regs_out0 60 KS_pDS KS_pDS_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PpDS.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PpDS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpDS.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PpDS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpDS.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PpDS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpDS.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PpDS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk' ZA Hag ltac:(clear - HV41l HV41r K8l K8r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K7l K7r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K9l K9r) | clear; lia]. 
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PpDL := LibSegBs_pDL_u.
Definition KS_pDL : list nat := Eval vm_compute in (BG.kept_list 60 PpDL.regs0 PpDL.regs_out0).
Lemma KS_pDL_ok : BG.kept_ok 60 PpDL.regs0 PpDL.regs_out0 KS_pDL = true. Proof. vm_compute. reflexivity. Qed.
Lemma pDL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 19) = Z_to_bv 64 (V 42%nat) -> getr R (reg 23) = Z_to_bv 64 (V 37%nat) ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 25 <= (V 37%nat) <= 134217728 ->
  4096 <= (V 42%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x58bc8 M) (st fx' R' 0x56720 M')
        /\ (forall x, In x KS_pDL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 363484
        /\ getr R' (reg 10) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 37%nat) + 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G19 G23 pvzI4 K1 K2 pvzI5 pvzI6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV37l; move HV37l before pvzI2; pose proof (proj2 pvzI2) as HV37r; move HV37r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV42l; move HV42l before pvzI3; pose proof (proj2 pvzI3) as HV42r; move HV42r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K3l; move K3l before pvzI5; pose proof (proj2 pvzI5) as K3r; move K3r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K4l; move K4l before pvzI6; pose proof (proj2 pvzI6) as K4r; move K4r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_42 := V 42%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 37%nat => Z_to_bv 64 vz_37 | 42%nat => Z_to_bv 64 vz_42 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 37%nat => vz_37 | 42%nat => vz_42 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 43%nat. }
  assert (HR: regs_ok E PpDL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PpDL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PpDL.kn0).
  { unfold know_ok, PpDL.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PpDL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PpDL.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PpDL.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PpDL.ps0) with 0x56720 in Hms. change (SR.ps_regs PpDL.ps0) with (map (fun i => (i, nth i PpDL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PpDL.ps0) with PpDL.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PpDL.regs0 PpDL.regs_out0 60 KS_pDL KS_pDL_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PpDL.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PpDL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpDL.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PpDL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PpDL.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PpDL.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PpF := LibSegBs_pF_u.
Definition KS_pF : list nat := Eval vm_compute in (BG.kept_list 60 PpF.regs0 PpF.regs_out0).
Lemma KS_pF_ok : BG.kept_ok 60 PpF.regs0 PpF.regs_out0 KS_pF = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma pF_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 43%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 20) = Z_to_bv 64 (V 41%nat) -> getr R (reg 21) = Z_to_bv 64 (V 40%nat) -> getr R (reg 22) = Z_to_bv 64 (V 38%nat) -> getr R (reg 24) = Z_to_bv 64 (V 56%nat) ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 140735332483072 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 24 -> (((V 2%nat) - 80) + 80 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 80)) -> 0 <= (V 34%nat) <= 134217728 ->
  4096 <= (V 41%nat) <= 140737488355328 -> 48 <= (V 40%nat) <= 134217728 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 10%nat) + 0) <= bv_unsigned a < ((V 10%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 10%nat) + 0) <= i < ((V 10%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x58bdc M) (st fx' R' 0xaba00 M')
        /\ (forall x, In x KS_pF -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 363520
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 34%nat) + (V 41%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 56%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 10%nat) + 16) (V 41%nat)
        /\ L5.u64_at RSEGS M' ((V 10%nat) + 8) (V 34%nat)
        /\ L5.u64_at RSEGS M' (V 10%nat) ((2 * ((V 40%nat) / 2)) + 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G8 G9 G10 G18 G20 G21 G22 G24 pvzI10 K1 K2 pvzI11 K4 K5 K6 pvzI12 pvzI13 pvzI14.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV40l; move HV40l before pvzI5; pose proof (proj2 pvzI5) as HV40r; move HV40r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV41l; move HV41l before pvzI6; pose proof (proj2 pvzI6) as HV41r; move HV41r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV43l; move HV43l before pvzI7; pose proof (proj2 pvzI7) as HV43r; move HV43r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV55l; move HV55l before pvzI8; pose proof (proj2 pvzI8) as HV55r; move HV55r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV56l; move HV56l before pvzI9; pose proof (proj2 pvzI9) as HV56r; move HV56r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K0l; move K0l before pvzI10; pose proof (proj2 pvzI10) as K0r; move K0r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K3l; move K3l before pvzI11; pose proof (proj2 pvzI11) as K3r; move K3r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K7l; move K7l before pvzI12; pose proof (proj2 pvzI12) as K7r; move K7r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K8l; move K8l before pvzI13; pose proof (proj2 pvzI13) as K8r; move K8r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K9l; move K9l before pvzI14; pose proof (proj2 pvzI14) as K9r; move K9r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 34%nat => Z_to_bv 64 vz_34 | 38%nat => Z_to_bv 64 vz_38 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 43%nat => Z_to_bv 64 vz_43 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 34%nat => vz_34 | 38%nat => vz_38 | 40%nat => vz_40 | 41%nat => vz_41 | 43%nat => vz_43 | 55%nat => vz_55 | 56%nat => vz_56 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 57%nat. }
  assert (HR: regs_ok E PpF.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PpF.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PpF.kn0).
  { unfold know_ok, PpF.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PpF.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PpF.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_10 + 0) <= bv_unsigned a < (vz_10 + 0) + 24) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PpF.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk' ZA Hag ltac:(clear) | clear - HV10l HV10r K3l K3r K6 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PpF.ps0) with 0xaba00 in Hms. change (SR.ps_regs PpF.ps0) with (map (fun i => (i, nth i PpF.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PpF.ps0) with PpF.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PpF.regs0 PpF.regs_out0 60 KS_pF KS_pF_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PpF.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PpF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpF.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PpF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpF.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PpF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PpF.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PpF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk' ZA Hag ltac:(clear - HV41l HV41r K8l K8r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K7l K7r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; cbn [In]; right; right; left; reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K9l K9r) | clear; lia]. 
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)

End PMSRZP.
