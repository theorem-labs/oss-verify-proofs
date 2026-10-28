(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BigLinkZA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0PlanKit_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanPlanCore
     BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import XIcptA_b XIcptAs0Kit_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require LibSegBa_aicC1_b LibSegBa_aicC2_b LibSegBa_aicCs1_b LibSegBa_aicCl1a_b LibSegBa_aicCl1b_b LibSegBa_aicCl2_b LibSegBa_aicCl3_b LibSegBa_aicCs2_b LibSegBa_aicCl4_b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PMAISP.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).

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
Module PaicC1 := LibSegBa_aicC1_b.
Definition KS_aicC1 : list nat := Eval vm_compute in (BG.kept_list 60 PaicC1.regs0 PaicC1.regs_out0).
Lemma KS_aicC1_ok : BG.kept_ok 60 PaicC1.regs0 PaicC1.regs_out0 KS_aicC1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma aicC1_conc (HFILL : XIAS0.fill_spec) (HCOPY : XIAS0.copy_spec) (HTLS : XIAS0.tls_spec) fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + 24) -> getr R (reg 18) = Z_to_bv 64 8 -> getr R (reg 19) = Z_to_bv 64 8 -> getr R (reg 20) = Z_to_bv 64 ((V 33%nat) - 64) -> getr R (reg 21) = Z_to_bv 64 ((((V 33%nat) + 16) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 1265600 -> getr R (reg 23) = Z_to_bv 64 2147450880 -> getr R (reg 24) = Z_to_bv 64 2147450880 -> getr R (reg 25) = Z_to_bv 64 1265968 -> getr R (reg 26) = Z_to_bv 64 ((((V 33%nat) + 120) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 1266008 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5.img_clear M 1249280 1282048 ->
  L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 6905920 <= (V 33%nat) <= 140737488355048 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 272 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 34 -> L5.writable RSEGS M (V 33%nat) 272 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 272 <= ((V 2%nat) - 4096)) ->
  (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 272 <= 65536) -> (((V 2%nat) - 4096) + 4096 <= ((V 33%nat) - 64) \/ ((V 33%nat) - 64) + 24 <= ((V 2%nat) - 4096)) -> (65536 + 6840320 <= ((V 33%nat) - 64) \/ ((V 33%nat) - 64) + 24 <= 65536) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac2a8 M) (st fx' R' 0x78130 M')
        /\ (forall x, In x KS_aicC1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 705208
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 32)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 48).
Proof.
  intros pvzI1 pvzI2 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 pvzI3 K1 K2 K3 K4 K5 pvzI4 K7 K8 K9 K10 K11 K12 K13 K14.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as K0l; move K0l before pvzI3; pose proof (proj2 pvzI3) as K0r; move K0r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K6l; move K6l before pvzI4; pose proof (proj2 pvzI4) as K6r; move K6r before pvzI4; clear pvzI4.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 34%nat. }
  assert (HR: regs_ok E PaicC1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaicC1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaicC1.kn0).
  { unfold know_ok, PaicC1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaicC1.seg_sound_ax HFILL HCOPY HTLS fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaicC1.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PaicC1.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaicC1.ps0) with 0x78130 in Hms. change (SR.ps_regs PaicC1.ps0) with (map (fun i => (i, nth i PaicC1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaicC1.ps0) with PaicC1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaicC1.regs0 PaicC1.regs_out0 60 KS_aicC1 KS_aicC1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaicC1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaicC1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicC1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaicC1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicC1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaicC1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PaicC1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PaicC1.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PaicC2 := LibSegBa_aicC2_b.
Definition KS_aicC2 : list nat := Eval vm_compute in (BG.kept_list 60 PaicC2.regs0 PaicC2.regs_out0).
Lemma KS_aicC2_ok : BG.kept_ok 60 PaicC2.regs0 PaicC2.regs_out0 KS_aicC2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma aicC2_conc (HFILL : XIAS0.fill_spec) (HCOPY : XIAS0.copy_spec) (HTLS : XIAS0.tls_spec) fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + 24) -> getr R (reg 18) = Z_to_bv 64 8 -> getr R (reg 19) = Z_to_bv 64 8 -> getr R (reg 20) = Z_to_bv 64 ((V 33%nat) - 64) -> getr R (reg 21) = Z_to_bv 64 ((((V 33%nat) + 16) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 1265600 -> getr R (reg 23) = Z_to_bv 64 2147450880 -> getr R (reg 24) = Z_to_bv 64 2147450880 -> getr R (reg 25) = Z_to_bv 64 1265968 -> getr R (reg 26) = Z_to_bv 64 ((((V 33%nat) + 120) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 1266008 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5.img_clear M 1249280 1282048 ->
  L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 6905920 <= (V 33%nat) <= 140737488355048 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 272 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 34 -> L5.writable RSEGS M (V 33%nat) 272 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 272 <= ((V 2%nat) - 4096)) ->
  (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 272 <= 65536) -> (((V 2%nat) - 4096) + 4096 <= ((V 33%nat) - 64) \/ ((V 33%nat) - 64) + 24 <= ((V 2%nat) - 4096)) -> (65536 + 6840320 <= ((V 33%nat) - 64) \/ ((V 33%nat) - 64) + 24 <= 65536) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 16) <= bv_unsigned a < ((V 33%nat) + 16) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 16) <= i < ((V 33%nat) + 16) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac2b8 M) (st fx' R' 0x78130 M')
        /\ (forall x, In x KS_aicC2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 705252
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 80)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 24
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 33%nat) + 80)
        /\ getr R' (reg 21) = Z_to_bv 64 ((((V 33%nat) + 16) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 16) 1265728).
Proof.
  intros pvzI1 pvzI2 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 pvzI3 K1 K2 K3 K4 K5 pvzI4 K7 K8 K9 K10 K11 K12 K13 K14.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as K0l; move K0l before pvzI3; pose proof (proj2 pvzI3) as K0r; move K0r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K6l; move K6l before pvzI4; pose proof (proj2 pvzI4) as K6r; move K6r before pvzI4; clear pvzI4.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 34%nat. }
  assert (HR: regs_ok E PaicC2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaicC2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaicC2.kn0).
  { unfold know_ok, PaicC2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaicC2.seg_sound_ax HFILL HCOPY HTLS fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaicC2.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_33 + 16) <= bv_unsigned a < (vz_33 + 16) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PaicC2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaicC2.ps0) with 0x78130 in Hms. change (SR.ps_regs PaicC2.ps0) with (map (fun i => (i, nth i PaicC2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaicC2.ps0) with PaicC2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaicC2.regs0 PaicC2.regs_out0 60 KS_aicC2 KS_aicC2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaicC2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaicC2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicC2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaicC2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicC2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaicC2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicC2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PaicC2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicC2.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaicC2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicC2.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PaicC2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PaicCs1 := LibSegBa_aicCs1_b.
Definition KS_aicCs1 : list nat := Eval vm_compute in (BG.kept_list 60 PaicCs1.regs0 PaicCs1.regs_out0).
Lemma KS_aicCs1_ok : BG.kept_ok 60 PaicCs1.regs0 PaicCs1.regs_out0 KS_aicCs1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma aicCs1_conc (HFILL : XIAS0.fill_spec) (HCOPY : XIAS0.copy_spec) (HTLS : XIAS0.tls_spec) fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + 24) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + 80) -> getr R (reg 19) = Z_to_bv 64 8 -> getr R (reg 20) = Z_to_bv 64 ((V 33%nat) - 64) -> getr R (reg 21) = Z_to_bv 64 ((((V 33%nat) + 16) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 1265600 -> getr R (reg 23) = Z_to_bv 64 2147450880 -> getr R (reg 24) = Z_to_bv 64 2147450880 -> getr R (reg 25) = Z_to_bv 64 1265968 -> getr R (reg 26) = Z_to_bv 64 ((((V 33%nat) + 120) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 1266008 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5.img_clear M 1249280 1282048 ->
  L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 6905920 <= (V 33%nat) <= 140737488355048 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 272 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 34 -> L5.writable RSEGS M (V 33%nat) 272 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 272 <= ((V 2%nat) - 4096)) ->
  (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 272 <= 65536) -> (((V 2%nat) - 4096) + 4096 <= ((V 33%nat) - 64) \/ ((V 33%nat) - 64) + 24 <= ((V 2%nat) - 4096)) -> (65536 + 6840320 <= ((V 33%nat) - 64) \/ ((V 33%nat) - 64) + 24 <= 65536) -> L5.u8_at RSEGS M ((V 33%nat) - 64) (V 38%nat) ->
  0 <= (V 38%nat) <= 255 -> Z.testbit (V 38%nat) 0 = false -> L5.u64_at RSEGS M ((V 33%nat) - 64) (V 35%nat) -> L5.u64_at RSEGS M ((V 33%nat) - 56) (V 36%nat) ->
  L5.u64_at RSEGS M ((V 33%nat) - 48) (V 37%nat) -> L5.u8_at RSEGS M ((V 33%nat) + 80) 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 80) <= bv_unsigned a < ((V 33%nat) + 80) + 36) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 80) <= i < ((V 33%nat) + 80) + 36) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac2e4 M) (st fx' R' 0xac320 M')
        /\ (forall x, In x KS_aicCs1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 705312
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 80)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 80) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 88) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 96) (V 37%nat)
        /\ L5.u32_at RSEGS M' ((V 33%nat) + 112) 8).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 pvzI7 K1 K2 K3 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 K14 K15 pvzI9 K17 K18 K19 K20 K21.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K16l; move K16l before pvzI9; pose proof (proj2 pvzI9) as K16r; move K16r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 39%nat. }
  assert (HR: regs_ok E PaicCs1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaicCs1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaicCs1.kn0).
  { unfold know_ok, PaicCs1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear - HV38l HV38r K16l K16r) | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | byte_tac ltac:(clear - HV38l HV38r K16l K16r) | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV38l HV38r K16l K16r) | clear; lia | erewrite L5K.land1_bit0_false by first [exact K17 | (clear - HV38l HV38r K16l K16r; lia)]; clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear - HV35l HV35r) | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear - HV37l HV37r) | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | byte_tac ltac:(clear) | exactA K21]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaicCs1.seg_sound_ax HFILL HCOPY HTLS fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaicCs1.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_33 + 80) <= bv_unsigned a < (vz_33 + 80) + 36) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PaicCs1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaicCs1.ps0) with 0xac320 in Hms. change (SR.ps_regs PaicCs1.ps0) with (map (fun i => (i, nth i PaicCs1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaicCs1.ps0) with PaicCs1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaicCs1.regs0 PaicCs1.regs_out0 60 KS_aicCs1 KS_aicCs1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaicCs1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaicCs1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCs1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaicCs1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCs1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaicCs1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCs1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PaicCs1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCs1.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PaicCs1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCs1.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PaicCs1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk' ZA Hag ltac:(clear - HV35l HV35r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk' ZA Hag ltac:(clear - HV36l HV36r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk' ZA Hag ltac:(clear - HV37l HV37r) | clear; lia]. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PaicCl1a := LibSegBa_aicCl1a_b.
Definition KS_aicCl1a : list nat := Eval vm_compute in (BG.kept_list 60 PaicCl1a.regs0 PaicCl1a.regs_out0).
Lemma KS_aicCl1a_ok : BG.kept_ok 60 PaicCl1a.regs0 PaicCl1a.regs_out0 KS_aicCl1a = true. Proof. vm_compute. reflexivity. Qed.
Lemma aicCl1a_conc (HFILL : XIAS0.fill_spec) (HCOPY : XIAS0.copy_spec) (HTLS : XIAS0.tls_spec) fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + 24) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + 80) -> getr R (reg 19) = Z_to_bv 64 8 -> getr R (reg 20) = Z_to_bv 64 ((V 33%nat) - 64) -> getr R (reg 21) = Z_to_bv 64 ((((V 33%nat) + 16) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 1265600 -> getr R (reg 23) = Z_to_bv 64 2147450880 -> getr R (reg 24) = Z_to_bv 64 2147450880 -> getr R (reg 25) = Z_to_bv 64 1265968 -> getr R (reg 26) = Z_to_bv 64 ((((V 33%nat) + 120) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 1266008 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5.img_clear M 1249280 1282048 ->
  L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 6905920 <= (V 33%nat) <= 140737488355048 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 272 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 34 -> L5.writable RSEGS M (V 33%nat) 272 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 272 <= ((V 2%nat) - 4096)) ->
  (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 272 <= 65536) -> (((V 2%nat) - 4096) + 4096 <= ((V 33%nat) - 64) \/ ((V 33%nat) - 64) + 24 <= ((V 2%nat) - 4096)) -> (65536 + 6840320 <= ((V 33%nat) - 64) \/ ((V 33%nat) - 64) + 24 <= 65536) -> L5.u8_at RSEGS M ((V 33%nat) - 64) (V 38%nat) ->
  0 <= (V 38%nat) <= 255 -> Z.testbit (V 38%nat) 0 = true -> L5.u64_at RSEGS M ((V 33%nat) - 56) (V 40%nat) -> L5.u64_at RSEGS M ((V 33%nat) - 48) (V 36%nat) ->
  L5.u8_at RSEGS M ((V 33%nat) + 80) 0 -> 23 <= (V 40%nat) <= 44 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 240) <= bv_unsigned a < ((V 2%nat) - 240) + 48) -> ~ (((V 33%nat) + 104) <= bv_unsigned a < ((V 33%nat) + 104) + 8) -> ~ (((V 33%nat) + 112) <= bv_unsigned a < ((V 33%nat) + 112) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 240) <= i < ((V 2%nat) - 240) + 48) -> ~ (((V 33%nat) + 104) <= i < ((V 33%nat) + 104) + 8) -> ~ (((V 33%nat) + 112) <= i < ((V 33%nat) + 112) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac2e4 M) (st fx' R' 0x130338 M')
        /\ (forall x, In x KS_aicCl1a -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 876768
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 240)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 33%nat) + 80)
        /\ getr R' (reg 10) = Z_to_bv 64 48
        /\ getr R' (reg 11) = Z_to_bv 64 44
        /\ getr R' (reg 12) = Z_to_bv 64 30
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 19) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 47
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) ((V 33%nat) - 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) 8
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) ((V 33%nat) + 80)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) ((V 33%nat) + 24)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) ((V 33%nat) + 16)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 705312
        /\ L5.u32_at RSEGS M' ((V 33%nat) + 112) 8).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 pvzI6 K1 K2 K3 K4 K5 pvzI7 K7 K8 K9 K10 K11 K12 K13 K14 K15 pvzI8 K17 K18 K19 K20 pvzI9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV40l; move HV40l before pvzI5; pose proof (proj2 pvzI5) as HV40r; move HV40r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K6l; move K6l before pvzI7; pose proof (proj2 pvzI7) as K6r; move K6r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K16l; move K16l before pvzI8; pose proof (proj2 pvzI8) as K16r; move K16r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K21l; move K21l before pvzI9; pose proof (proj2 pvzI9) as K21r; move K21r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_40 := V 40%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 40%nat => Z_to_bv 64 vz_40 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 36%nat => vz_36 | 38%nat => vz_38 | 40%nat => vz_40 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 41%nat. }
  assert (HR: regs_ok E PaicCl1a.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaicCl1a.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaicCl1a.kn0).
  { unfold know_ok, PaicCl1a.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear - HV38l HV38r K16l K16r) | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | byte_tac ltac:(clear - HV38l HV38r K16l K16r) | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV38l HV38r K16l K16r) | clear; lia | erewrite L5K.land1_bit0_true by first [exact K17 | (clear - HV38l HV38r K16l K16r; lia)]; clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear - HV40l HV40r K21l K21r) | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | byte_tac ltac:(clear) | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaicCl1a.seg_sound_ax HFILL HCOPY HTLS fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaicCl1a.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 240) <= bv_unsigned a < (vz_2 - 240) + 48) -> ~ ((vz_33 + 104) <= bv_unsigned a < (vz_33 + 104) + 8) -> ~ ((vz_33 + 112) <= bv_unsigned a < (vz_33 + 112) + 4) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PaicCl1a.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K13 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaicCl1a.ps0) with 0x130338 in Hms. change (SR.ps_regs PaicCl1a.ps0) with (map (fun i => (i, nth i PaicCl1a.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaicCl1a.ps0) with PaicCl1a.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaicCl1a.regs0 PaicCl1a.regs_out0 60 KS_aicCl1a KS_aicCl1a_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaicCl1a.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaicCl1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl1a.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaicCl1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl1a.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaicCl1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl1a.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PaicCl1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl1a.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaicCl1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl1a.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaicCl1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl1a.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PaicCl1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl1a.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PaicCl1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl1a.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PaicCl1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl1a.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaicCl1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl1a.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PaicCl1a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PaicCl1b := LibSegBa_aicCl1b_b.
Definition KS_aicCl1b : list nat := Eval vm_compute in (BG.kept_list 60 PaicCl1b.regs0 PaicCl1b.regs_out0).
Lemma KS_aicCl1b_ok : BG.kept_ok 60 PaicCl1b.regs0 PaicCl1b.regs_out0 KS_aicCl1b = true. Proof. vm_compute. reflexivity. Qed.
Lemma aicCl1b_conc (HFILL : XIAS0.fill_spec) (HCOPY : XIAS0.copy_spec) (HTLS : XIAS0.tls_spec) fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + 24) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + 80) -> getr R (reg 19) = Z_to_bv 64 8 -> getr R (reg 20) = Z_to_bv 64 ((V 33%nat) - 64) -> getr R (reg 21) = Z_to_bv 64 ((((V 33%nat) + 16) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 1265600 -> getr R (reg 23) = Z_to_bv 64 2147450880 -> getr R (reg 24) = Z_to_bv 64 2147450880 -> getr R (reg 25) = Z_to_bv 64 1265968 -> getr R (reg 26) = Z_to_bv 64 ((((V 33%nat) + 120) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 1266008 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5.img_clear M 1249280 1282048 ->
  L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 6905920 <= (V 33%nat) <= 140737488355048 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 272 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 34 -> L5.writable RSEGS M (V 33%nat) 272 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 272 <= ((V 2%nat) - 4096)) ->
  (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 272 <= 65536) -> (((V 2%nat) - 4096) + 4096 <= ((V 33%nat) - 64) \/ ((V 33%nat) - 64) + 24 <= ((V 2%nat) - 4096)) -> (65536 + 6840320 <= ((V 33%nat) - 64) \/ ((V 33%nat) - 64) + 24 <= 65536) -> L5.u8_at RSEGS M ((V 33%nat) - 64) (V 38%nat) ->
  0 <= (V 38%nat) <= 255 -> Z.testbit (V 38%nat) 0 = true -> L5.u64_at RSEGS M ((V 33%nat) - 56) (V 40%nat) -> L5.u64_at RSEGS M ((V 33%nat) - 48) (V 36%nat) ->
  L5.u8_at RSEGS M ((V 33%nat) + 80) 0 -> 45 <= (V 40%nat) <= 67108863 -> 47 <= (Z.lor (V 40%nat) 7) <= 67108871 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 240) <= bv_unsigned a < ((V 2%nat) - 240) + 48) -> ~ (((V 33%nat) + 104) <= bv_unsigned a < ((V 33%nat) + 104) + 8) -> ~ (((V 33%nat) + 112) <= bv_unsigned a < ((V 33%nat) + 112) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 240) <= i < ((V 2%nat) - 240) + 48) -> ~ (((V 33%nat) + 104) <= i < ((V 33%nat) + 104) + 8) -> ~ (((V 33%nat) + 112) <= i < ((V 33%nat) + 112) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac2e4 M) (st fx' R' 0x130338 M')
        /\ (forall x, In x KS_aicCl1b -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 876768
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 240)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 33%nat) + 80)
        /\ getr R' (reg 10) = Z_to_bv 64 ((8 * ((V 40%nat) / 8)) + 8)
        /\ getr R' (reg 11) = Z_to_bv 64 44
        /\ getr R' (reg 12) = Z_to_bv 64 30
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 19) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 ((8 * ((V 40%nat) / 8)) + 7)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) ((V 33%nat) - 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) 8
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) ((V 33%nat) + 80)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) ((V 33%nat) + 24)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) ((V 33%nat) + 16)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 705312
        /\ L5.u32_at RSEGS M' ((V 33%nat) + 112) 8).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 pvzI6 K1 K2 K3 K4 K5 pvzI7 K7 K8 K9 K10 K11 K12 K13 K14 K15 pvzI8 K17 K18 K19 K20 pvzI9 pvzI10.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV40l; move HV40l before pvzI5; pose proof (proj2 pvzI5) as HV40r; move HV40r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K6l; move K6l before pvzI7; pose proof (proj2 pvzI7) as K6r; move K6r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K16l; move K16l before pvzI8; pose proof (proj2 pvzI8) as K16r; move K16r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K21l; move K21l before pvzI9; pose proof (proj2 pvzI9) as K21r; move K21r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K22l; move K22l before pvzI10; pose proof (proj2 pvzI10) as K22r; move K22r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_40 := V 40%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 40%nat => Z_to_bv 64 vz_40 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 36%nat => vz_36 | 38%nat => vz_38 | 40%nat => vz_40 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 41%nat. }
  assert (HR: regs_ok E PaicCl1b.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaicCl1b.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaicCl1b.kn0).
  { unfold know_ok, PaicCl1b.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear - HV38l HV38r K16l K16r) | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | byte_tac ltac:(clear - HV38l HV38r K16l K16r) | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV38l HV38r K16l K16r) | clear; lia | erewrite L5K.land1_bit0_true by first [exact K17 | (clear - HV38l HV38r K16l K16r; lia)]; clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear - HV40l HV40r K21l K21r K22l K22r) | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | byte_tac ltac:(clear) | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K21l K21r K22l K22r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact (conj K22l K22r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaicCl1b.seg_sound_ax HFILL HCOPY HTLS fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaicCl1b.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 240) <= bv_unsigned a < (vz_2 - 240) + 48) -> ~ ((vz_33 + 104) <= bv_unsigned a < (vz_33 + 104) + 8) -> ~ ((vz_33 + 112) <= bv_unsigned a < (vz_33 + 112) + 4) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PaicCl1b.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K13 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaicCl1b.ps0) with 0x130338 in Hms. change (SR.ps_regs PaicCl1b.ps0) with (map (fun i => (i, nth i PaicCl1b.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaicCl1b.ps0) with PaicCl1b.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaicCl1b.regs0 PaicCl1b.regs_out0 60 KS_aicCl1b KS_aicCl1b_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaicCl1b.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaicCl1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl1b.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaicCl1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl1b.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaicCl1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl1b.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PaicCl1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl1b.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaicCl1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl1b.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaicCl1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl1b.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PaicCl1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl1b.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PaicCl1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl1b.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PaicCl1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl1b.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaicCl1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl1b.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PaicCl1b.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PaicCl2 := LibSegBa_aicCl2_b.
Definition KS_aicCl2 : list nat := Eval vm_compute in (BG.kept_list 60 PaicCl2.regs0 PaicCl2.regs_out0).
Lemma KS_aicCl2_ok : BG.kept_ok 60 PaicCl2.regs0 PaicCl2.regs_out0 KS_aicCl2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma aicCl2_conc (HFILL : XIAS0.fill_spec) (HCOPY : XIAS0.copy_spec) (HTLS : XIAS0.tls_spec) fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 240) -> getr R (reg 8) = Z_to_bv 64 (V 40%nat) -> getr R (reg 10) = Z_to_bv 64 (V 41%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xd60e0 M) (st fx' R' 0x77c90 M')
        /\ (forall x, In x KS_aicCl2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 876784
        /\ getr R' (reg 11) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 41%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G10 G19.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV40l; move HV40l before pvzI3; pose proof (proj2 pvzI3) as HV40r; move HV40r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV41l; move HV41l before pvzI4; pose proof (proj2 pvzI4) as HV41r; move HV41r before pvzI4; clear pvzI4.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => (V 2%nat) | 36%nat => (V 36%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E PaicCl2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaicCl2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaicCl2.kn0).
  { unfold know_ok, PaicCl2.kn0.
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaicCl2.seg_sound_ax HFILL HCOPY HTLS fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaicCl2.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PaicCl2.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaicCl2.ps0) with 0x77c90 in Hms. change (SR.ps_regs PaicCl2.ps0) with (map (fun i => (i, nth i PaicCl2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaicCl2.ps0) with PaicCl2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaicCl2.regs0 PaicCl2.regs_out0 60 KS_aicCl2 KS_aicCl2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaicCl2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaicCl2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaicCl2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PaicCl2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PaicCl2.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaicCl2.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PaicCl3 := LibSegBa_aicCl3_b.
Definition KS_aicCl3 : list nat := Eval vm_compute in (BG.kept_list 60 PaicCl3.regs0 PaicCl3.regs_out0).
Lemma KS_aicCl3_ok : BG.kept_ok 60 PaicCl3.regs0 PaicCl3.regs_out0 KS_aicCl3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma aicCl3_conc (HFILL : XIAS0.fill_spec) (HCOPY : XIAS0.copy_spec) (HTLS : XIAS0.tls_spec) fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 240) -> getr R (reg 8) = Z_to_bv 64 (V 40%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + 80) -> getr R (reg 18) = Z_to_bv 64 (V 41%nat) -> getr R (reg 20) = Z_to_bv 64 (V 42%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> 6905920 <= (V 33%nat) <= 140737488355048 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 272 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 34 -> L5.writable RSEGS M (V 33%nat) 272 ->
  (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 272 <= ((V 2%nat) - 4096)) -> (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 272 <= 65536) -> (((V 2%nat) - 4096) + 4096 <= ((V 33%nat) - 64) \/ ((V 33%nat) - 64) + 24 <= ((V 2%nat) - 4096)) -> (65536 + 6840320 <= ((V 33%nat) - 64) \/ ((V 33%nat) - 64) + 24 <= 65536) ->
  L5.u64_at RSEGS M ((V 2%nat) - 200) 705312 -> L5.u64_at RSEGS M ((V 2%nat) - 208) ((V 33%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 216) ((V 33%nat) + 24) -> L5.u64_at RSEGS M ((V 2%nat) - 224) ((V 33%nat) + 80) ->
  L5.u64_at RSEGS M ((V 2%nat) - 232) 8 -> L5.u64_at RSEGS M ((V 2%nat) - 240) ((V 33%nat) - 64) -> 4096 <= (V 41%nat) <= 140737488355328 -> 23 <= (V 40%nat) <= 67108863 ->
  47 <= (V 42%nat) <= 67108871 -> L5.writable RSEGS M ((V 41%nat) + (V 40%nat)) 1 -> (((V 2%nat) - 4096) + 4096 <= ((V 41%nat) + (V 40%nat)) \/ ((V 41%nat) + (V 40%nat)) + 1 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 272 <= ((V 41%nat) + (V 40%nat)) \/ ((V 41%nat) + (V 40%nat)) + 1 <= (V 33%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 80) <= bv_unsigned a < ((V 33%nat) + 80) + 24) -> ~ ((((V 41%nat) + (V 40%nat)) + 0) <= bv_unsigned a < (((V 41%nat) + (V 40%nat)) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 80) <= i < ((V 33%nat) + 80) + 24) -> ~ ((((V 41%nat) + (V 40%nat)) + 0) <= i < (((V 41%nat) + (V 40%nat)) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xd60f0 M) (st fx' R' 0xac320 M')
        /\ (forall x, In x KS_aicCl3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 705312
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 192)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 33%nat) + 24)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 80)
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 33%nat) + 80)
        /\ getr R' (reg 19) = Z_to_bv 64 8
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 33%nat) - 64)
        /\ L5.u8_at RSEGS M' ((V 40%nat) + (V 41%nat)) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 96) (V 41%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 88) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 80) ((V 42%nat) + 2)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G18 G20 pvzI6 K1 K2 pvzI7 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 pvzI8 pvzI9 pvzI10 K21 K22 K23.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV40l; move HV40l before pvzI3; pose proof (proj2 pvzI3) as HV40r; move HV40r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV41l; move HV41l before pvzI4; pose proof (proj2 pvzI4) as HV41r; move HV41r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV42l; move HV42l before pvzI5; pose proof (proj2 pvzI5) as HV42r; move HV42r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K18l; move K18l before pvzI8; pose proof (proj2 pvzI8) as K18r; move K18r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K19l; move K19l before pvzI9; pose proof (proj2 pvzI9) as K19r; move K19r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K20l; move K20l before pvzI10; pose proof (proj2 pvzI10) as K20r; move K20r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 40%nat => vz_40 | 41%nat => vz_41 | 42%nat => vz_42 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 43%nat. }
  assert (HR: regs_ok E PaicCl3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaicCl3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaicCl3.kn0).
  { unfold know_ok, PaicCl3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8 K10 K22) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8 K10 K22) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8 K10 K22) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K8 K10 K22; lia | clear - HV2l HV2r K0l K0r K8 K10 K22; lia | clear - HV2l HV2r K0l K0r K8 K10 K22; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K8 K9 K10 K11 K23) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K8 K9 K10 K11 K23) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K8 K9 K10 K11 K23) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K8 K9 K10 K11 K23) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5 K8 K9 K10 K11 K23; lia | clear - HV33l HV33r K3l K3r K5 K8 K9 K10 K11 K23; lia | clear - HV33l HV33r K3l K3r K5 K8 K9 K10 K11 K23; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K8 K9 K10 K11 K23) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5 K8 K9 K10 K11 K23; lia | clear - HV33l HV33r K3l K3r K5 K8 K9 K10 K11 K23; lia | clear - HV33l HV33r K3l K3r K5 K8 K9 K10 K11 K23; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8 K10 K22) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K8 K9 K10 K11 K23) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K8 K9 K10 K11 K23) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8 K10 K22) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K8 K9 K10 K11 K23) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K8 K9 K10 K11 K23) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8 K10 K22) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K8 K10 K22; lia | clear - HV2l HV2r K0l K0r K8 K10 K22; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8 K10 K22) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K8 K9 K10 K11 K23) | clear - HV2l HV2r K0l K0r K8 K10 K22; lia | clear - HV2l HV2r K0l K0r K8 K10 K22; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8 K10 K22) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K8 K9 K10 K11 K23) | clear - HV2l HV2r K0l K0r K8 K10 K22; lia | clear - HV2l HV2r K0l K0r K8 K10 K22; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8 K10 K22) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K8 K9 K10 K11 K23) | clear - HV2l HV2r K0l K0r K8 K10 K22; lia | clear - HV2l HV2r K0l K0r K8 K10 K22; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8 K10 K22) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K8 K10 K22; lia | clear - HV2l HV2r K0l K0r K8 K10 K22; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8 K10 K22) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K8 K9 K10 K11 K23) | clear - HV2l HV2r K0l K0r K8 K10 K22; lia | clear - HV2l HV2r K0l K0r K8 K10 K22; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K18l K18r K22 K23) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K22 K23) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K22 K23 HV41l HV41r K18l K18r) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K19l K19r K22 K23 HV41l HV41r K18l K18r; lia | clear - HV40l HV40r K19l K19r K22 K23 HV41l HV41r K18l K18r; lia | clear - HV40l HV40r K19l K19r K22 K23 HV41l HV41r K18l K18r; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K8 K10 K22) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K22 K23 HV41l HV41r K18l K18r) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K8 K9 K10 K11 K23) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K22 K23 HV41l HV41r K18l K18r) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaicCl3.seg_sound_ax HFILL HCOPY HTLS fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaicCl3.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_33 + 80) <= bv_unsigned a < (vz_33 + 80) + 24) -> ~ (((vz_41 + vz_40) + 0) <= bv_unsigned a < ((vz_41 + vz_40) + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PaicCl3.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5 K8 K9 K10 K11 K23) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K3l K3r K5 K8 K9 K10 K11 K23 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K22 K23 HV41l HV41r K18l K18r) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K19l K19r K22 K23 HV41l HV41r K18l K18r Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaicCl3.ps0) with 0xac320 in Hms. change (SR.ps_regs PaicCl3.ps0) with (map (fun i => (i, nth i PaicCl3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaicCl3.ps0) with PaicCl3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaicCl3.regs0 PaicCl3.regs_out0 60 KS_aicCl3 KS_aicCl3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaicCl3.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaicCl3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl3.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaicCl3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl3.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaicCl3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl3.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PaicCl3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaicCl3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl3.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaicCl3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl3.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaicCl3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl3.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PaicCl3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K22 K23 HV41l HV41r K18l K18r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5 K8 K9 K10 K11 K23) | evalEk' ZA Hag ltac:(clear - HV41l HV41r K18l K18r K22 K23) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5 K8 K9 K10 K11 K23) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r K22 K23) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5 K8 K9 K10 K11 K23) | evalEk' ZA Hag ltac:(clear - HV42l HV42r K20l K20r) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PaicCs2 := LibSegBa_aicCs2_b.
Definition KS_aicCs2 : list nat := Eval vm_compute in (BG.kept_list 60 PaicCs2.regs0 PaicCs2.regs_out0).
Lemma KS_aicCs2_ok : BG.kept_ok 60 PaicCs2.regs0 PaicCs2.regs_out0 KS_aicCs2 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma aicCs2_conc (HFILL : XIAS0.fill_spec) (HCOPY : XIAS0.copy_spec) (HTLS : XIAS0.tls_spec) fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 16) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5.img_clear M 1249280 1282048 ->
  L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 6905920 <= (V 33%nat) <= 140737488355048 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 272 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 34 -> L5.writable RSEGS M (V 33%nat) 272 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 272 <= ((V 2%nat) - 4096)) ->
  (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 272 <= 65536) -> (((V 2%nat) - 4096) + 4096 <= ((V 33%nat) - 64) \/ ((V 33%nat) - 64) + 24 <= ((V 2%nat) - 4096)) -> (65536 + 6840320 <= ((V 33%nat) - 64) \/ ((V 33%nat) - 64) + 24 <= 65536) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 691528 ->
  L5.u64_at RSEGS M ((V 2%nat) - 128) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((V 33%nat) + 120) -> L5.u64_at RSEGS M ((V 2%nat) - 144) 8 -> L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 33%nat) - 64) ->
  L5.u64_at RSEGS M ((V 2%nat) - 160) 1266032 -> L5.u64_at RSEGS M ((V 2%nat) - 168) ((V 33%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 120) -> L5.u64_at RSEGS M ((V 2%nat) - 184) (((V 33%nat) / 8) + 2147450880) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 72) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 53%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 54%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 104) (V 55%nat) -> L5.u8_at RSEGS M ((V 33%nat) + 80) (V 38%nat) -> 0 <= (V 38%nat) <= 44 -> Z.testbit (V 38%nat) 0 = false ->
  L5.u32_at RSEGS M ((V 33%nat) + 112) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 272) <= bv_unsigned a < ((V 2%nat) - 272) + 80) -> ~ (((V 33%nat) + 32) <= bv_unsigned a < ((V 33%nat) + 32) + 24) -> ~ (((V 33%nat) + 104) <= bv_unsigned a < ((V 33%nat) + 104) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 272) <= i < ((V 2%nat) - 272) + 80) -> ~ (((V 33%nat) + 32) <= i < ((V 33%nat) + 32) + 24) -> ~ (((V 33%nat) + 104) <= i < ((V 33%nat) + 104) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac320 M) (st fx' R' 0xa8d80 M')
        /\ (forall x, In x KS_aicCs2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 104)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 48)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 ((((V 33%nat) + 104) / 8) + 2147450880)
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 15) = Z_to_bv 64 (((V 33%nat) + ((V 38%nat) / 2)) + 81)
        /\ getr R' (reg 16) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 53%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 54%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 55%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 48) (((V 33%nat) + ((V 38%nat) / 2)) + 81)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 40) ((V 33%nat) + 81)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 32) ((V 33%nat) + 81)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 104) (((V 33%nat) + ((V 38%nat) / 2)) + 81)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 G2 G8 pvzI17 K1 K2 K3 K4 K5 pvzI18 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 pvzI19 K39 K40.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV43l; move HV43l before pvzI4; pose proof (proj2 pvzI4) as HV43r; move HV43r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV44l; move HV44l before pvzI5; pose proof (proj2 pvzI5) as HV44r; move HV44r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV45l; move HV45l before pvzI6; pose proof (proj2 pvzI6) as HV45r; move HV45r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV46l; move HV46l before pvzI7; pose proof (proj2 pvzI7) as HV46r; move HV46r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV47l; move HV47l before pvzI8; pose proof (proj2 pvzI8) as HV47r; move HV47r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV48l; move HV48l before pvzI9; pose proof (proj2 pvzI9) as HV48r; move HV48r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV49l; move HV49l before pvzI10; pose proof (proj2 pvzI10) as HV49r; move HV49r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV50l; move HV50l before pvzI11; pose proof (proj2 pvzI11) as HV50r; move HV50r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV51l; move HV51l before pvzI12; pose proof (proj2 pvzI12) as HV51r; move HV51r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV52l; move HV52l before pvzI13; pose proof (proj2 pvzI13) as HV52r; move HV52r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV53l; move HV53l before pvzI14; pose proof (proj2 pvzI14) as HV53r; move HV53r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV54l; move HV54l before pvzI15; pose proof (proj2 pvzI15) as HV54r; move HV54r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV55l; move HV55l before pvzI16; pose proof (proj2 pvzI16) as HV55r; move HV55r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K0l; move K0l before pvzI17; pose proof (proj2 pvzI17) as K0r; move K0r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K6l; move K6l before pvzI18; pose proof (proj2 pvzI18) as K6r; move K6r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K38l; move K38l before pvzI19; pose proof (proj2 pvzI19) as K38r; move K38r before pvzI19; clear pvzI19.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *. set (vz_54 := V 54%nat) in *. set (vz_55 := V 55%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 38%nat => Z_to_bv 64 vz_38 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | 54%nat => Z_to_bv 64 vz_54 | 55%nat => Z_to_bv 64 vz_55 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 38%nat => vz_38 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | 53%nat => vz_53 | 54%nat => vz_54 | 55%nat => vz_55 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 56%nat. }
  assert (HR: regs_ok E PaicCs2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaicCs2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaicCs2.kn0).
  { unfold know_ok, PaicCs2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear - HV54l HV54r) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear - HV55l HV55r) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear - HV38l HV38r K38l K38r) | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | byte_tac ltac:(clear - HV38l HV38r K38l K38r) | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K38l K38r) | exact (conj K38l K38r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV38l HV38r K38l K38r) | clear; lia | erewrite L5K.land1_bit0_false by first [exact K39 | (clear - HV38l HV38r K38l K38r; lia)]; clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | exactA K40]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaicCs2.seg_sound_ax HFILL HCOPY HTLS fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaicCs2.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 272) <= bv_unsigned a < (vz_2 - 272) + 80) -> ~ ((vz_33 + 32) <= bv_unsigned a < (vz_33 + 32) + 24) -> ~ ((vz_33 + 104) <= bv_unsigned a < (vz_33 + 104) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PaicCs2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K13 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaicCs2.ps0) with 0xa8d80 in Hms. change (SR.ps_regs PaicCs2.ps0) with (map (fun i => (i, nth i PaicCs2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaicCs2.ps0) with PaicCs2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaicCs2.regs0 PaicCs2.regs_out0 60 KS_aicCs2 KS_aicCs2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaicCs2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaicCs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCs2.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaicCs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCs2.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaicCs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCs2.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PaicCs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCs2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaicCs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCs2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaicCs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCs2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PaicCs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCs2.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PaicCs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCs2.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PaicCs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCs2.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PaicCs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCs2.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PaicCs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCs2.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaicCs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCs2.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaicCs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCs2.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PaicCs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCs2.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PaicCs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCs2.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PaicCs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCs2.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PaicCs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCs2.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PaicCs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCs2.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PaicCs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCs2.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PaicCs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCs2.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PaicCs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14 HV38l HV38r K38l K38r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14 HV38l HV38r K38l K38r) | clear; lia].
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PaicCl4 := LibSegBa_aicCl4_b.
Definition KS_aicCl4 : list nat := Eval vm_compute in (BG.kept_list 60 PaicCl4.regs0 PaicCl4.regs_out0).
Lemma KS_aicCl4_ok : BG.kept_ok 60 PaicCl4.regs0 PaicCl4.regs_out0 KS_aicCl4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma aicCl4_conc (HFILL : XIAS0.fill_spec) (HCOPY : XIAS0.copy_spec) (HTLS : XIAS0.tls_spec) fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 16) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5.img_clear M 1249280 1282048 ->
  L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 6905920 <= (V 33%nat) <= 140737488355048 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 272 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 34 -> L5.writable RSEGS M (V 33%nat) 272 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 272 <= ((V 2%nat) - 4096)) ->
  (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 272 <= 65536) -> (((V 2%nat) - 4096) + 4096 <= ((V 33%nat) - 64) \/ ((V 33%nat) - 64) + 24 <= ((V 2%nat) - 4096)) -> (65536 + 6840320 <= ((V 33%nat) - 64) \/ ((V 33%nat) - 64) + 24 <= 65536) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 691528 ->
  L5.u64_at RSEGS M ((V 2%nat) - 128) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((V 33%nat) + 120) -> L5.u64_at RSEGS M ((V 2%nat) - 144) 8 -> L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 33%nat) - 64) ->
  L5.u64_at RSEGS M ((V 2%nat) - 160) 1266032 -> L5.u64_at RSEGS M ((V 2%nat) - 168) ((V 33%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 120) -> L5.u64_at RSEGS M ((V 2%nat) - 184) (((V 33%nat) / 8) + 2147450880) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 72) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 53%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 54%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 104) (V 55%nat) -> L5.u8_at RSEGS M ((V 33%nat) + 80) (V 38%nat) -> 0 <= (V 38%nat) <= 255 -> Z.testbit (V 38%nat) 0 = true ->
  L5.u64_at RSEGS M ((V 33%nat) + 88) (V 40%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 96) (V 41%nat) -> L5.u32_at RSEGS M ((V 33%nat) + 112) 8 -> 4096 <= (V 41%nat) <= 140737488355328 ->
  23 <= (V 40%nat) <= 67108863 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 272) <= bv_unsigned a < ((V 2%nat) - 272) + 80) -> ~ (((V 33%nat) + 32) <= bv_unsigned a < ((V 33%nat) + 32) + 24) -> ~ (((V 33%nat) + 104) <= bv_unsigned a < ((V 33%nat) + 104) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 272) <= i < ((V 2%nat) - 272) + 80) -> ~ (((V 33%nat) + 32) <= i < ((V 33%nat) + 32) + 24) -> ~ (((V 33%nat) + 104) <= i < ((V 33%nat) + 104) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xac320 M) (st fx' R' 0xa8d80 M')
        /\ (forall x, In x KS_aicCl4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 104)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 48)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 ((((V 33%nat) + 104) / 8) + 2147450880)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 15) = Z_to_bv 64 ((V 40%nat) + (V 41%nat))
        /\ getr R' (reg 16) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 53%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 54%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 55%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 48) ((V 40%nat) + (V 41%nat))
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 40) (V 41%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 32) (V 41%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 104) ((V 40%nat) + (V 41%nat))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 G2 G8 pvzI19 K1 K2 K3 K4 K5 pvzI20 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 pvzI21 K39 K40 K41 K42 pvzI22 pvzI23.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV40l; move HV40l before pvzI4; pose proof (proj2 pvzI4) as HV40r; move HV40r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV41l; move HV41l before pvzI5; pose proof (proj2 pvzI5) as HV41r; move HV41r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV43l; move HV43l before pvzI6; pose proof (proj2 pvzI6) as HV43r; move HV43r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV44l; move HV44l before pvzI7; pose proof (proj2 pvzI7) as HV44r; move HV44r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV45l; move HV45l before pvzI8; pose proof (proj2 pvzI8) as HV45r; move HV45r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV46l; move HV46l before pvzI9; pose proof (proj2 pvzI9) as HV46r; move HV46r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV47l; move HV47l before pvzI10; pose proof (proj2 pvzI10) as HV47r; move HV47r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV48l; move HV48l before pvzI11; pose proof (proj2 pvzI11) as HV48r; move HV48r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV49l; move HV49l before pvzI12; pose proof (proj2 pvzI12) as HV49r; move HV49r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV50l; move HV50l before pvzI13; pose proof (proj2 pvzI13) as HV50r; move HV50r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV51l; move HV51l before pvzI14; pose proof (proj2 pvzI14) as HV51r; move HV51r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV52l; move HV52l before pvzI15; pose proof (proj2 pvzI15) as HV52r; move HV52r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV53l; move HV53l before pvzI16; pose proof (proj2 pvzI16) as HV53r; move HV53r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV54l; move HV54l before pvzI17; pose proof (proj2 pvzI17) as HV54r; move HV54r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV55l; move HV55l before pvzI18; pose proof (proj2 pvzI18) as HV55r; move HV55r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K0l; move K0l before pvzI19; pose proof (proj2 pvzI19) as K0r; move K0r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K6l; move K6l before pvzI20; pose proof (proj2 pvzI20) as K6r; move K6r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K38l; move K38l before pvzI21; pose proof (proj2 pvzI21) as K38r; move K38r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K43l; move K43l before pvzI22; pose proof (proj2 pvzI22) as K43r; move K43r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K44l; move K44l before pvzI23; pose proof (proj2 pvzI23) as K44r; move K44r before pvzI23; clear pvzI23.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *. set (vz_54 := V 54%nat) in *. set (vz_55 := V 55%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 38%nat => Z_to_bv 64 vz_38 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | 54%nat => Z_to_bv 64 vz_54 | 55%nat => Z_to_bv 64 vz_55 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 38%nat => vz_38 | 40%nat => vz_40 | 41%nat => vz_41 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | 53%nat => vz_53 | 54%nat => vz_54 | 55%nat => vz_55 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 56%nat. }
  assert (HR: regs_ok E PaicCl4.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaicCl4.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaicCl4.kn0).
  { unfold know_ok, PaicCl4.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear - HV54l HV54r) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk ZA ltac:(clear - HV55l HV55r) | clear - HV2l HV2r K0l K0r K11 K13; lia | clear - HV2l HV2r K0l K0r K11 K13; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear - HV38l HV38r K38l K38r) | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | byte_tac ltac:(clear - HV38l HV38r K38l K38r) | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K38l K38r) | exact (conj K38l K38r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV38l HV38r K38l K38r) | clear; lia | erewrite L5K.land1_bit0_true by first [exact K39 | (clear - HV38l HV38r K38l K38r; lia)]; clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear - HV40l HV40r K44l K44r) | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear - HV41l HV41r K43l K43r) | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K43l K43r) | exact (conj K43l K43r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K44l K44r) | exact (conj K44l K44r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaicCl4.seg_sound_ax HFILL HCOPY HTLS fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaicCl4.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 272) <= bv_unsigned a < (vz_2 - 272) + 80) -> ~ ((vz_33 + 32) <= bv_unsigned a < (vz_33 + 32) + 24) -> ~ ((vz_33 + 104) <= bv_unsigned a < (vz_33 + 104) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PaicCl4.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K13) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K13 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaicCl4.ps0) with 0xa8d80 in Hms. change (SR.ps_regs PaicCl4.ps0) with (map (fun i => (i, nth i PaicCl4.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaicCl4.ps0) with PaicCl4.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaicCl4.regs0 PaicCl4.regs_out0 60 KS_aicCl4 KS_aicCl4_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaicCl4.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaicCl4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl4.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaicCl4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl4.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaicCl4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl4.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PaicCl4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl4.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaicCl4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl4.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaicCl4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl4.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PaicCl4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl4.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PaicCl4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl4.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PaicCl4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl4.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PaicCl4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl4.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PaicCl4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl4.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaicCl4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl4.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaicCl4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl4.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PaicCl4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl4.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PaicCl4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl4.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PaicCl4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl4.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PaicCl4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl4.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PaicCl4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl4.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PaicCl4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl4.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PaicCl4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaicCl4.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PaicCl4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K44l K44r HV41l HV41r K43l K43r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk' ZA Hag ltac:(clear - HV41l HV41r K43l K43r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk' ZA Hag ltac:(clear - HV41l HV41r K43l K43r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K13 K14) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K44l K44r HV41l HV41r K43l K43r) | clear; lia].
Qed.
(* [comment removed for export] *)

End PMAISP.
