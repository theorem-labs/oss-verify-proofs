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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require LibSegBa_afnA_b LibSegBa_afnB_b LibSegBa_afnPL_b LibSegBa_afnPM_b LibSegBa_afnNM_b LibSegBa_afnD_b LibSegBa_afnR1_b LibSegBa_afnQB_b LibSegBa_afnQR_b LibSegBa_afnT_b LibSegBa_afnZ_b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNAFIP.
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
Module PafnA := LibSegBa_afnA_b.
Definition KS_afnA : list nat := Eval vm_compute in (BG.kept_list 80 PafnA.regs0 PafnA.regs_out0).
Lemma KS_afnA_ok : BG.kept_ok 80 PafnA.regs0 PafnA.regs_out0 KS_afnA = true. Proof. vm_compute. reflexivity. Qed.
Lemma afnA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 34%nat) -> getr R (reg 11) = Z_to_bv 64 (V 33%nat) ->
  L5.img_clear M 1249280 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb6200 M) (st fx' R' 0x5df30 M')
        /\ (forall x, In x KS_afnA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 746096
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 10) = Z_to_bv 64 416
        /\ getr R' (reg 11) = Z_to_bv 64 1309752
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 20) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 2147450880
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
  intros pvzI1 pvzI2 pvzI3 G2 G10 G11 K0 K1 K2 pvzI4 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K3l; move K3l before pvzI4; pose proof (proj2 pvzI4) as K3r; move K3r before pvzI4; clear pvzI4.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 35%nat. }
  assert (HR: regs_ok E PafnA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PafnA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PafnA.kn0).
  { unfold know_ok, PafnA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PafnA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PafnA.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 128) <= bv_unsigned a < (vz_2 - 128) + 128) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PafnA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PafnA.ps0) with 0x5df30 in Hms. change (SR.ps_regs PafnA.ps0) with (map (fun i => (i, nth i PafnA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PafnA.ps0) with PafnA.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PafnA.regs0 PafnA.regs_out0 80 KS_afnA KS_afnA_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PafnA.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PafnA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafnA.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PafnA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafnA.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PafnA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafnA.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PafnA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafnA.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PafnA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafnA.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PafnA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafnA.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PafnA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafnA.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PafnA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafnA.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PafnA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafnA.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PafnA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
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
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PafnB := LibSegBa_afnB_b.
Definition KS_afnB_0 : list nat := Eval vm_compute in (BG.kept_list 80 PafnB.regs0 PafnB.regs_out0).
Lemma KS_afnB_0_ok : BG.kept_ok 80 PafnB.regs0 PafnB.regs_out0 KS_afnB_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_afnB_1 : list nat := Eval vm_compute in (BG.kept_list 80 PafnB.regs0 PafnB.regs_out1).
Lemma KS_afnB_1_ok : BG.kept_ok 80 PafnB.regs0 PafnB.regs_out1 KS_afnB_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma afnB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 24) = Z_to_bv 64 2147450880 ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6905856 <= (V 50%nat) <= 140737488354816 ->
  aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 512 -> L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) ->
  L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 50%nat) + 504) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 512 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 128) + 128 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 128)) ->
  (65536 + 6840320 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) -> (65536 + 6840320 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= 65536) -> (65536 + 6840320 <= (V 51%nat) \/ (V 51%nat) + 1 <= 65536) -> 0 <= (V 34%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 104) <= bv_unsigned a < ((V 2%nat) - 104) + 8) -> ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 24) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 104) <= i < ((V 2%nat) - 104) + 8) -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 24) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb6270 M) (st fx' R' 0xb63e0 M')
        /\ (forall x, In x KS_afnB_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 10
        /\ getr R' (reg 11) = Z_to_bv 64 14757395259826634752
        /\ getr R' (reg 12) = Z_to_bv 64 254
        /\ getr R' (reg 13) = Z_to_bv 64 7
        /\ getr R' (reg 14) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 18446744073709551601
        /\ getr R' (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 0
        /\ getr R' (reg 23) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 ((V 50%nat) + 32)
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450911) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450910) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450909) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450908) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450915) 7
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450914) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450913) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450912) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450903) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450902) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450901) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450900) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450907) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450906) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450905) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450904) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450895) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450894) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450893) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450892) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450899) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450898) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450897) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450896) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450891) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450890) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450889) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450888) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450887) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450886) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450885) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450884) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450931) 243
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450930) 243
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450929) 243
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450928) 243
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450923) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450922) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450921) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450920) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450927) 243
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450926) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450925) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450924) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450919) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450918) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450917) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450916) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450883) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450882) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450881) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450880) 241
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 16) 745984
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 8) 139344
        /\ L5.u64_at RSEGS M' (V 50%nat) 1102416563
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 50%nat)
        /\ L5.defined M' ((V 50%nat) + 24) 488)
      \/ (msteps RSEGS (st fx R 0xb6270 M) (st fx' R' 0xb6430 M')
        /\ (forall x, In x KS_afnB_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 10
        /\ getr R' (reg 11) = Z_to_bv 64 18446744073709551596
        /\ getr R' (reg 12) = Z_to_bv 64 1717986919
        /\ getr R' (reg 13) = Z_to_bv 64 254
        /\ getr R' (reg 14) = Z_to_bv 64 745984
        /\ getr R' (reg 15) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 0
        /\ getr R' (reg 23) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 ((V 50%nat) + 32)
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450911) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450910) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450909) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450908) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450915) 7
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450914) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450913) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450912) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450903) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450902) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450901) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450900) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450907) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450906) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450905) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450904) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450895) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450894) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450893) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450892) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450899) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450898) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450897) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450896) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450891) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450890) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450889) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450888) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450887) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450886) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450885) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450884) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450931) 243
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450930) 243
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450929) 243
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450928) 243
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450923) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450922) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450921) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450920) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450927) 243
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450926) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450925) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450924) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450919) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450918) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450917) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450916) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450883) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450882) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450881) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450880) 241
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 16) 745984
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 8) 139344
        /\ L5.u64_at RSEGS M' (V 50%nat) 1102416563
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 50%nat)
        /\ L5.defined M' ((V 50%nat) + 24) 488)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G20 G22 G24 pvzI6 K1 K2 pvzI7 K4 K5 K6 K7 K8 K9 pvzI8 K11 K12 K13 K14 K15 K16 K17 K18 pvzI9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV50l; move HV50l before pvzI4; pose proof (proj2 pvzI4) as HV50r; move HV50r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV51l; move HV51l before pvzI5; pose proof (proj2 pvzI5) as HV51r; move HV51r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K10l; move K10l before pvzI8; pose proof (proj2 pvzI8) as K10r; move K10r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K19l; move K19l before pvzI9; pose proof (proj2 pvzI9) as K19r; move K19r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PafnB.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PafnB.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PafnB.kn0).
  { unfold know_ok, PafnB.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K10l K10r K12 K13 K15 K18; lia | clear - HV51l HV51r K10l K10r K12 K13 K15 K18; lia | clear - HV51l HV51r K10l K10r K12 K13 K15 K18; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PafnB.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PafnB.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 104) <= bv_unsigned a < (vz_2 - 104) + 8) -> ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 24) -> ~ ((((vz_50 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 0) + 64) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PafnB.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K14 K15 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PafnB.ps0) with 0xb63e0 in Hms. change (SR.ps_regs PafnB.ps0) with (map (fun i => (i, nth i PafnB.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PafnB.ps0) with PafnB.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PafnB.regs0 PafnB.regs_out0 80 KS_afnB_0 KS_afnB_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PafnB.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PafnB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PafnB.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PafnB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PafnB.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PafnB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PafnB.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PafnB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PafnB.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PafnB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PafnB.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PafnB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PafnB.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PafnB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PafnB.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PafnB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PafnB.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PafnB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PafnB.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PafnB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PafnB.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PafnB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 23%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 24%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 25%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 26%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 27%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 28%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 29%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 30%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 31%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 32%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 33%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
    split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 34%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
    split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 35%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
    split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 36%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
    split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 41%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
    split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 42%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
    split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 43%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
    split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 44%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
    split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 37%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
    split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 38%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
    split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 39%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
    split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 40%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
    split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 45%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
    split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 46%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
    split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 47%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
    split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 48%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
    split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 49%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
    split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 50%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
    split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 51%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
    split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 52%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 53%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 54%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 55%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 56%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | clear; lia]. }
    eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 57%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
  - right.
    change (SR.ps_pc PafnB.ps1) with 0xb6430 in Hms. change (SR.ps_regs PafnB.ps1) with (map (fun i => (i, nth i PafnB.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PafnB.ps1) with PafnB.cells1 in Hcells. unfold PafnB.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PafnB.regs0 PafnB.regs_out1 80 KS_afnB_1 KS_afnB_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PafnB.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PafnB.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PafnB.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PafnB.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PafnB.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PafnB.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PafnB.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PafnB.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PafnB.regs_out1 E' R' 14 Hregs) by (clear; lia). cbn [nth PafnB.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PafnB.regs_out1 E' R' 15 Hregs) by (clear; lia). cbn [nth PafnB.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PafnB.regs_out1 E' R' 18 Hregs) by (clear; lia). cbn [nth PafnB.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PafnB.regs_out1 E' R' 19 Hregs) by (clear; lia). cbn [nth PafnB.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PafnB.regs_out1 E' R' 21 Hregs) by (clear; lia). cbn [nth PafnB.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PafnB.regs_out1 E' R' 23 Hregs) by (clear; lia). cbn [nth PafnB.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PafnB.regs_out1 E' R' 25 Hregs) by (clear; lia). cbn [nth PafnB.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 23%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 24%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 25%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 26%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 27%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 28%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 29%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 30%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 31%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 32%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 33%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
    split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 34%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
    split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 35%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
    split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 36%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
    split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 41%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
    split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 42%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
    split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 43%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
    split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 44%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
    split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 37%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
    split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 38%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
    split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 39%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
    split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 40%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
    split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 45%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
    split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 46%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
    split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 47%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
    split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 48%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
    split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 49%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
    split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 50%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
    split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 51%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
    split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 52%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 53%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 54%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 55%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 56%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | clear; lia]. }
    eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 57%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PafnPL := LibSegBa_afnPL_b.
Definition KS_afnPL : list nat := Eval vm_compute in (BG.kept_list 80 PafnPL.regs0 PafnPL.regs_out0).
Lemma KS_afnPL_ok : BG.kept_ok 80 PafnPL.regs0 PafnPL.regs_out0 KS_afnPL = true. Proof. vm_compute. reflexivity. Qed.
Lemma afnPL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 10 -> getr R (reg 11) = Z_to_bv 64 14757395259826634752 -> getr R (reg 12) = Z_to_bv 64 254 -> getr R (reg 14) = Z_to_bv 64 (V 36%nat) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 (V 35%nat) -> getr R (reg 23) = Z_to_bv 64 (V 50%nat) -> getr R (reg 24) = Z_to_bv 64 2147450880 -> getr R (reg 25) = Z_to_bv 64 ((V 50%nat) + 32) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6905856 <= (V 50%nat) <= 140737488354816 ->
  aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 512 -> L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) ->
  L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 50%nat) + 504) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 512 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 128) + 128 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 128)) ->
  (65536 + 6840320 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) -> (65536 + 6840320 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= 65536) -> (65536 + 6840320 <= (V 51%nat) \/ (V 51%nat) + 1 <= 65536) -> 0 <= (V 36%nat) <= 2147483647 ->
  0 <= (V 35%nat) <= 10 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 32) <= bv_unsigned a < ((V 50%nat) + 32) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 32) <= i < ((V 50%nat) + 32) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb63e0 M) (st fx' R' 0xb640c M')
        /\ (forall x, In x KS_afnPL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 13) = Z_to_bv 64 (V 35%nat)
        /\ bv_unsigned (getr R' (reg 14)) = (((((4294967296 * (V 36%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)
        /\ getr R' (reg 15) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 16) = Z_to_bv 64 (((V 35%nat) + (V 50%nat)) + 32)
        /\ bv_unsigned (getr R' (reg 17)) = (((Z.land (((V 36%nat) + ((18446744073709551606 * (((((4294967296 * (V 36%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64) 18446744073709551567) + 48) mod 2 ^ 64)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 35%nat) + 1)
        /\ L5.u8_at RSEGS M' (((V 35%nat) + (V 50%nat)) + 32) (((Z.land (((V 36%nat) + ((18446744073709551606 * (((((4294967296 * (V 36%nat)) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368)) mod 2 ^ 64)) mod 2 ^ 64) 18446744073709551567) + 48) mod 2 ^ 64)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G10 G11 G12 G14 G18 G19 G20 G21 G23 G24 G25 pvzI7 K1 K2 pvzI8 K4 K5 K6 K7 K8 K9 pvzI9 K11 K12 K13 K14 K15 K16 K17 K18 pvzI10 pvzI11.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K10l; move K10l before pvzI9; pose proof (proj2 pvzI9) as K10r; move K10r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K19l; move K19l before pvzI10; pose proof (proj2 pvzI10) as K19r; move K19r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K20l; move K20l before pvzI11; pose proof (proj2 pvzI11) as K20r; move K20r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PafnPL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PafnPL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PafnPL.kn0).
  { unfold know_ok, PafnPL.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K10l K10r K12 K13 K15 K18; lia | clear - HV51l HV51r K10l K10r K12 K13 K15 K18; lia | clear - HV51l HV51r K10l K10r K12 K13 K15 K18; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PafnPL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PafnPL.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_50 + 32) <= bv_unsigned a < (vz_50 + 32) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PafnPL.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PafnPL.ps0) with 0xb640c in Hms. change (SR.ps_regs PafnPL.ps0) with (map (fun i => (i, nth i PafnPL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PafnPL.ps0) with PafnPL.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PafnPL.regs0 PafnPL.regs_out0 80 KS_afnPL KS_afnPL_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PafnPL.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PafnPL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafnPL.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PafnPL.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
  split. { rewrite (BG.out_reg PafnPL.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PafnPL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafnPL.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PafnPL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafnPL.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PafnPL.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
  split. { rewrite (BG.out_reg PafnPL.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PafnPL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV35l HV35r K20l K20r HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | byte_tac ltac:(clear - HV36l HV36r K19l K19r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PafnPM := LibSegBa_afnPM_b.
Definition KS_afnPM_0 : list nat := Eval vm_compute in (BG.kept_list 80 PafnPM.regs0 PafnPM.regs_out0).
Lemma KS_afnPM_0_ok : BG.kept_ok 80 PafnPM.regs0 PafnPM.regs_out0 KS_afnPM_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_afnPM_1 : list nat := Eval vm_compute in (BG.kept_list 80 PafnPM.regs0 PafnPM.regs_out1).
Lemma KS_afnPM_1_ok : BG.kept_ok 80 PafnPM.regs0 PafnPM.regs_out1 KS_afnPM_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma afnPM_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 10 -> getr R (reg 12) = Z_to_bv 64 254 -> getr R (reg 13) = Z_to_bv 64 (V 35%nat) -> getr R (reg 15) = Z_to_bv 64 (V 36%nat) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 23) = Z_to_bv 64 (V 50%nat) -> getr R (reg 24) = Z_to_bv 64 2147450880 -> getr R (reg 25) = Z_to_bv 64 ((V 50%nat) + 32) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 0 <= (V 36%nat) <= 2147483647 ->
  0 <= (V 35%nat) <= 10 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb640c M) (st fx' R' 0xb63e0 M')
        /\ (forall x, In x KS_afnPM_0 -> getr R' (reg x) = getr R (reg x))
        /\ 10 <= (V 36%nat))
      \/ (msteps RSEGS (st fx R 0xb640c M) (st fx' R' 0xb646c M')
        /\ (forall x, In x KS_afnPM_1 -> getr R' (reg x) = getr R (reg x))
        /\ (V 36%nat) < 10)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G12 G13 G15 G18 G19 G20 G23 G24 G25 pvzI6 K1 K2 pvzI7 pvzI8.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PafnPM.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PafnPM.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PafnPM.kn0).
  { unfold know_ok, PafnPM.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PafnPM.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PafnPM.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PafnPM.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PafnPM.ps0) with 0xb63e0 in Hms. change (SR.ps_regs PafnPM.ps0) with (map (fun i => (i, nth i PafnPM.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PafnPM.ps0) with PafnPM.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PafnPM.regs0 PafnPM.regs_out0 80 KS_afnPM_0 KS_afnPM_0_ok HR Hag Hregs j Hj). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  - right.
    change (SR.ps_pc PafnPM.ps1) with 0xb646c in Hms. change (SR.ps_regs PafnPM.ps1) with (map (fun i => (i, nth i PafnPM.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PafnPM.ps1) with PafnPM.cells1 in Hcells. unfold PafnPM.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PafnPM.regs0 PafnPM.regs_out1 80 KS_afnPM_1 KS_afnPM_1_ok HR Hag Hregs j Hj). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PafnNM := LibSegBa_afnNM_b.
Definition KS_afnNM_0 : list nat := Eval vm_compute in (BG.kept_list 80 PafnNM.regs0 PafnNM.regs_out0).
Lemma KS_afnNM_0_ok : BG.kept_ok 80 PafnNM.regs0 PafnNM.regs_out0 KS_afnNM_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_afnNM_1 : list nat := Eval vm_compute in (BG.kept_list 80 PafnNM.regs0 PafnNM.regs_out1).
Lemma KS_afnNM_1_ok : BG.kept_ok 80 PafnNM.regs0 PafnNM.regs_out1 KS_afnNM_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma afnNM_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 10 -> getr R (reg 11) = Z_to_bv 64 (-20) -> getr R (reg 12) = Z_to_bv 64 1717986919 -> getr R (reg 13) = Z_to_bv 64 254 -> getr R (reg 14) = Z_to_bv 64 (V 35%nat) -> getr R (reg 15) = Z_to_bv 64 (V 41%nat) -> getr R (reg 16) = Z_to_bv 64 (V 39%nat) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 23) = Z_to_bv 64 (V 50%nat) -> getr R (reg 24) = Z_to_bv 64 2147450880 -> getr R (reg 25) = Z_to_bv 64 ((V 50%nat) + 32) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 0 <= (V 35%nat) <= 10 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb6464 M) (st fx' R' 0xb6430 M')
        /\ (forall x, In x KS_afnNM_0 -> getr R' (reg x) = getr R (reg x))
        /\ (V 39%nat) <= 18446744073709551596)
      \/ (msteps RSEGS (st fx R 0xb6464 M) (st fx' R' 0xb646c M')
        /\ (forall x, In x KS_afnNM_1 -> getr R' (reg x) = getr R (reg x))
        /\ 18446744073709551596 < (V 39%nat))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G10 G11 G12 G13 G14 G15 G16 G18 G19 G20 G23 G24 G25 pvzI7 K1 K2 pvzI8.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV39l; move HV39l before pvzI4; pose proof (proj2 pvzI4) as HV39r; move HV39r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV41l; move HV41l before pvzI5; pose proof (proj2 pvzI5) as HV41r; move HV41r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV50l; move HV50l before pvzI6; pose proof (proj2 pvzI6) as HV50r; move HV50r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 39%nat => Z_to_bv 64 vz_39 | 41%nat => Z_to_bv 64 vz_41 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 39%nat => vz_39 | 41%nat => vz_41 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PafnNM.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PafnNM.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PafnNM.kn0).
  { unfold know_ok, PafnNM.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PafnNM.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PafnNM.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PafnNM.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PafnNM.ps0) with 0xb6430 in Hms. change (SR.ps_regs PafnNM.ps0) with (map (fun i => (i, nth i PafnNM.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PafnNM.ps0) with PafnNM.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PafnNM.regs0 PafnNM.regs_out0 80 KS_afnNM_0 KS_afnNM_0_ok HR Hag Hregs j Hj). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  - right.
    change (SR.ps_pc PafnNM.ps1) with 0xb646c in Hms. change (SR.ps_regs PafnNM.ps1) with (map (fun i => (i, nth i PafnNM.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PafnNM.ps1) with PafnNM.cells1 in Hcells. unfold PafnNM.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PafnNM.regs0 PafnNM.regs_out1 80 KS_afnNM_1 KS_afnNM_1_ok HR Hag Hregs j Hj). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PafnD := LibSegBa_afnD_b.
Definition KS_afnD_0 : list nat := Eval vm_compute in (BG.kept_list 80 PafnD.regs0 PafnD.regs_out0).
Lemma KS_afnD_0_ok : BG.kept_ok 80 PafnD.regs0 PafnD.regs_out0 KS_afnD_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_afnD_1 : list nat := Eval vm_compute in (BG.kept_list 80 PafnD.regs0 PafnD.regs_out1).
Lemma KS_afnD_1_ok : BG.kept_ok 80 PafnD.regs0 PafnD.regs_out1 KS_afnD_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma afnD_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 (V 35%nat) -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 (V 50%nat) -> getr R (reg 24) = Z_to_bv 64 2147450880 -> getr R (reg 25) = Z_to_bv 64 ((V 50%nat) + 32) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6905856 <= (V 50%nat) <= 140737488354816 ->
  aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 512 -> L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) ->
  L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 50%nat) + 504) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 512 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 128) + 128 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 128)) ->
  (65536 + 6840320 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) -> (65536 + 6840320 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= 65536) -> (65536 + 6840320 <= (V 51%nat) \/ (V 51%nat) + 1 <= 65536) -> 1 <= (V 35%nat) <= 10 ->
  0 <= (V 34%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb646c M) (st fx' R' 0xb64a0 M')
        /\ (forall x, In x KS_afnD_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 22) = Z_to_bv 64 (((V 35%nat) + (V 50%nat)) + 31)
        /\ getr R' (reg 26) = Z_to_bv 64 (((V 35%nat) + (V 50%nat)) + 31))
      \/ (msteps RSEGS (st fx R 0xb646c M) (st fx' R' 0xd5bc4 M')
        /\ (forall x, In x KS_afnD_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 746632
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 45
        /\ getr R' (reg 26) = Z_to_bv 64 (((V 35%nat) + (V 50%nat)) + 32))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 pvzI7 K1 K2 pvzI8 K4 K5 K6 K7 K8 K9 pvzI9 K11 K12 K13 K14 K15 K16 K17 K18 pvzI10 pvzI11.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K10l; move K10l before pvzI9; pose proof (proj2 pvzI9) as K10r; move K10r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K19l; move K19l before pvzI10; pose proof (proj2 pvzI10) as K19r; move K19r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K20l; move K20l before pvzI11; pose proof (proj2 pvzI11) as K20r; move K20r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PafnD.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PafnD.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PafnD.kn0).
  { unfold know_ok, PafnD.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K10l K10r K12 K13 K15 K18; lia | clear - HV51l HV51r K10l K10r K12 K13 K15 K18; lia | clear - HV51l HV51r K10l K10r K12 K13 K15 K18; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PafnD.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PafnD.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PafnD.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PafnD.ps0) with 0xb64a0 in Hms. change (SR.ps_regs PafnD.ps0) with (map (fun i => (i, nth i PafnD.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PafnD.ps0) with PafnD.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PafnD.regs0 PafnD.regs_out0 80 KS_afnD_0 KS_afnD_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PafnD.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PafnD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PafnD.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PafnD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PafnD.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PafnD.regs_out0]. first [reflexivity | wordP' ZA Hag].
  - right.
    change (SR.ps_pc PafnD.ps1) with 0xd5bc4 in Hms. change (SR.ps_regs PafnD.ps1) with (map (fun i => (i, nth i PafnD.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PafnD.ps1) with PafnD.cells1 in Hcells. unfold PafnD.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PafnD.regs0 PafnD.regs_out1 80 KS_afnD_1 KS_afnD_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PafnD.regs_out1 E' R' 1 Hregs) by (clear; lia). cbn [nth PafnD.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PafnD.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PafnD.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PafnD.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PafnD.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PafnD.regs_out1 E' R' 26 Hregs) by (clear; lia). cbn [nth PafnD.regs_out1]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PafnR1 := LibSegBa_afnR1_b.
Definition KS_afnR1 : list nat := Eval vm_compute in (BG.kept_list 80 PafnR1.regs0 PafnR1.regs_out0).
Lemma KS_afnR1_ok : BG.kept_ok 80 PafnR1.regs0 PafnR1.regs_out0 KS_afnR1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma afnR1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 (V 35%nat) -> getr R (reg 23) = Z_to_bv 64 (V 50%nat) -> getr R (reg 24) = Z_to_bv 64 2147450880 -> getr R (reg 25) = Z_to_bv 64 ((V 50%nat) + 32) -> getr R (reg 26) = Z_to_bv 64 (((V 50%nat) + 32) + (V 35%nat)) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6905856 <= (V 50%nat) <= 140737488354816 ->
  aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 512 -> L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) ->
  L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 50%nat) + 504) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 512 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 128) + 128 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 128)) ->
  (65536 + 6840320 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) -> (65536 + 6840320 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= 65536) -> (65536 + 6840320 <= (V 51%nat) \/ (V 51%nat) + 1 <= 65536) -> 1 <= (V 35%nat) <= 10 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb6488 M) (st fx' R' 0xb64a0 M')
        /\ (forall x, In x KS_afnR1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 35%nat) + 1)
        /\ getr R' (reg 22) = Z_to_bv 64 (((V 35%nat) + (V 50%nat)) + 31)
        /\ getr R' (reg 26) = Z_to_bv 64 (((V 35%nat) + (V 50%nat)) + 31)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G18 G19 G20 G21 G23 G24 G25 G26 pvzI6 K1 K2 pvzI7 K4 K5 K6 K7 K8 K9 pvzI8 K11 K12 K13 K14 K15 K16 K17 K18 pvzI9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV50l; move HV50l before pvzI4; pose proof (proj2 pvzI4) as HV50r; move HV50r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV51l; move HV51l before pvzI5; pose proof (proj2 pvzI5) as HV51r; move HV51r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K10l; move K10l before pvzI8; pose proof (proj2 pvzI8) as K10r; move K10r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K19l; move K19l before pvzI9; pose proof (proj2 pvzI9) as K19r; move K19r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PafnR1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PafnR1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PafnR1.kn0).
  { unfold know_ok, PafnR1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K10l K10r K12 K13 K15 K18; lia | clear - HV51l HV51r K10l K10r K12 K13 K15 K18; lia | clear - HV51l HV51r K10l K10r K12 K13 K15 K18; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PafnR1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PafnR1.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PafnR1.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PafnR1.ps0) with 0xb64a0 in Hms. change (SR.ps_regs PafnR1.ps0) with (map (fun i => (i, nth i PafnR1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PafnR1.ps0) with PafnR1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PafnR1.regs0 PafnR1.regs_out0 80 KS_afnR1 KS_afnR1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PafnR1.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PafnR1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafnR1.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PafnR1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PafnR1.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PafnR1.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PafnQB := LibSegBa_afnQB_b.
Definition KS_afnQB : list nat := Eval vm_compute in (BG.kept_list 80 PafnQB.regs0 PafnQB.regs_out0).
Lemma KS_afnQB_ok : BG.kept_ok 80 PafnQB.regs0 PafnQB.regs_out0 KS_afnQB = true. Proof. vm_compute. reflexivity. Qed.
Lemma afnQB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 22) = Z_to_bv 64 (((V 50%nat) + 32) + (V 40%nat)) -> getr R (reg 23) = Z_to_bv 64 (V 50%nat) -> getr R (reg 24) = Z_to_bv 64 2147450880 -> getr R (reg 25) = Z_to_bv 64 ((V 50%nat) + 32) -> getr R (reg 26) = Z_to_bv 64 (((V 50%nat) + 32) + (V 40%nat)) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6905856 <= (V 50%nat) <= 140737488354816 ->
  aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 512 -> L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) ->
  L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 50%nat) + 504) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 512 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 128) + 128 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 128)) ->
  (65536 + 6840320 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) -> (65536 + 6840320 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= 65536) -> (65536 + 6840320 <= (V 51%nat) \/ (V 51%nat) + 1 <= 65536) -> 0 <= (V 40%nat) <= 9 ->
  L5KA.zeros_at M (((((V 50%nat) + 32) + (V 40%nat)) / 8) + 2147450880) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb64a0 M) (st fx' R' 0xd5bc4 M')
        /\ (forall x, In x KS_afnQB -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 746684
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G18 G19 G20 G22 G23 G24 G25 G26 pvzI6 K1 K2 pvzI7 K4 K5 K6 K7 K8 K9 pvzI8 K11 K12 K13 K14 K15 K16 K17 K18 pvzI9 K20.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV40l; move HV40l before pvzI3; pose proof (proj2 pvzI3) as HV40r; move HV40r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV50l; move HV50l before pvzI4; pose proof (proj2 pvzI4) as HV50r; move HV50r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV51l; move HV51l before pvzI5; pose proof (proj2 pvzI5) as HV51r; move HV51r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K10l; move K10l before pvzI8; pose proof (proj2 pvzI8) as K10r; move K10r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K19l; move K19l before pvzI9; pose proof (proj2 pvzI9) as K19r; move K19r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 40%nat => Z_to_bv 64 vz_40 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 40%nat => vz_40 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PafnQB.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PafnQB.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PafnQB.kn0).
  { unfold know_ok, PafnQB.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K10l K10r K12 K13 K15 K18; lia | clear - HV51l HV51r K10l K10r K12 K13 K15 K18; lia | clear - HV51l HV51r K10l K10r K12 K13 K15 K18; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K19l K19r HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV40l HV40r K19l K19r HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV40l HV40r K19l K19r HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | exactA K20]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PafnQB.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PafnQB.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PafnQB.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PafnQB.ps0) with 0xd5bc4 in Hms. change (SR.ps_regs PafnQB.ps0) with (map (fun i => (i, nth i PafnQB.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PafnQB.ps0) with PafnQB.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PafnQB.regs0 PafnQB.regs_out0 80 KS_afnQB KS_afnQB_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PafnQB.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PafnQB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PafnQB.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PafnQB.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PafnQR := LibSegBa_afnQR_b.
Definition KS_afnQR_0 : list nat := Eval vm_compute in (BG.kept_list 80 PafnQR.regs0 PafnQR.regs_out0).
Lemma KS_afnQR_0_ok : BG.kept_ok 80 PafnQR.regs0 PafnQR.regs_out0 KS_afnQR_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_afnQR_1 : list nat := Eval vm_compute in (BG.kept_list 80 PafnQR.regs0 PafnQR.regs_out1).
Lemma KS_afnQR_1_ok : BG.kept_ok 80 PafnQR.regs0 PafnQR.regs_out1 KS_afnQR_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma afnQR_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 22) = Z_to_bv 64 (((V 50%nat) + 32) + (V 40%nat)) -> getr R (reg 23) = Z_to_bv 64 (V 50%nat) -> getr R (reg 24) = Z_to_bv 64 2147450880 -> getr R (reg 25) = Z_to_bv 64 ((V 50%nat) + 32) -> getr R (reg 26) = Z_to_bv 64 (((V 50%nat) + 32) + (V 40%nat)) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6905856 <= (V 50%nat) <= 140737488354816 ->
  aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 512 -> L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) ->
  L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 50%nat) + 504) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 512 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 128) + 128 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 128)) ->
  (65536 + 6840320 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) -> (65536 + 6840320 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= 65536) -> (65536 + 6840320 <= (V 51%nat) \/ (V 51%nat) + 1 <= 65536) -> 0 <= (V 40%nat) <= 9 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb64bc M) (st fx' R' 0xb64a0 M')
        /\ (forall x, In x KS_afnQR_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 22) = Z_to_bv 64 (((V 40%nat) + (V 50%nat)) + 31)
        /\ getr R' (reg 26) = Z_to_bv 64 (((V 40%nat) + (V 50%nat)) + 31)
        /\ (((V 50%nat) + 32) mod 2 ^ 64) <= (((((V 40%nat) + (V 50%nat)) mod 2 ^ 64) + 31) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xb64bc M) (st fx' R' 0xb64dc M')
        /\ (forall x, In x KS_afnQR_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 22) = Z_to_bv 64 (((V 40%nat) + (V 50%nat)) + 31)
        /\ getr R' (reg 26) = Z_to_bv 64 (((V 40%nat) + (V 50%nat)) + 31)
        /\ (((((V 40%nat) + (V 50%nat)) mod 2 ^ 64) + 31) mod 2 ^ 64) < (((V 50%nat) + 32) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G18 G19 G20 G22 G23 G24 G25 G26 pvzI6 K1 K2 pvzI7 K4 K5 K6 K7 K8 K9 pvzI8 K11 K12 K13 K14 K15 K16 K17 K18 pvzI9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV40l; move HV40l before pvzI3; pose proof (proj2 pvzI3) as HV40r; move HV40r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV50l; move HV50l before pvzI4; pose proof (proj2 pvzI4) as HV50r; move HV50r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV51l; move HV51l before pvzI5; pose proof (proj2 pvzI5) as HV51r; move HV51r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K10l; move K10l before pvzI8; pose proof (proj2 pvzI8) as K10r; move K10r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K19l; move K19l before pvzI9; pose proof (proj2 pvzI9) as K19r; move K19r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 40%nat => Z_to_bv 64 vz_40 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 40%nat => vz_40 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PafnQR.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PafnQR.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PafnQR.kn0).
  { unfold know_ok, PafnQR.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K10l K10r K12 K13 K15 K18; lia | clear - HV51l HV51r K10l K10r K12 K13 K15 K18; lia | clear - HV51l HV51r K10l K10r K12 K13 K15 K18; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PafnQR.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PafnQR.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PafnQR.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PafnQR.ps0) with 0xb64a0 in Hms. change (SR.ps_regs PafnQR.ps0) with (map (fun i => (i, nth i PafnQR.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PafnQR.ps0) with PafnQR.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PafnQR.regs0 PafnQR.regs_out0 80 KS_afnQR_0 KS_afnQR_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PafnQR.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PafnQR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PafnQR.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PafnQR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  - right.
    change (SR.ps_pc PafnQR.ps1) with 0xb64dc in Hms. change (SR.ps_regs PafnQR.ps1) with (map (fun i => (i, nth i PafnQR.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PafnQR.ps1) with PafnQR.cells1 in Hcells. unfold PafnQR.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PafnQR.regs0 PafnQR.regs_out1 80 KS_afnQR_1 KS_afnQR_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PafnQR.regs_out1 E' R' 22 Hregs) by (clear; lia). cbn [nth PafnQR.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PafnQR.regs_out1 E' R' 26 Hregs) by (clear; lia). cbn [nth PafnQR.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PafnT := LibSegBa_afnT_b.
Definition KS_afnT : list nat := Eval vm_compute in (BG.kept_list 80 PafnT.regs0 PafnT.regs_out0).
Lemma KS_afnT_ok : BG.kept_ok 80 PafnT.regs0 PafnT.regs_out0 KS_afnT = true. Proof. vm_compute. reflexivity. Qed.
Lemma afnT_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 (V 35%nat) -> getr R (reg 23) = Z_to_bv 64 (V 50%nat) -> getr R (reg 24) = Z_to_bv 64 2147450880 -> getr R (reg 25) = Z_to_bv 64 ((V 50%nat) + 32) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6905856 <= (V 50%nat) <= 140737488354816 ->
  aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 512 -> L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) ->
  L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 50%nat) + 504) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 512 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 128) + 128 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 128)) ->
  (65536 + 6840320 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) -> (65536 + 6840320 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= 65536) -> (65536 + 6840320 <= (V 51%nat) \/ (V 51%nat) + 1 <= 65536) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb64dc M) (st fx' R' 0x7b90c M')
        /\ (forall x, In x KS_afnT -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 746876
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880)
        /\ getr R' (reg 11) = Z_to_bv 64 64
        /\ L5.u64_at RSEGS M' (V 50%nat) 1172321806
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450911) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450910) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450909) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450908) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450915) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450914) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450913) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450912) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450903) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450902) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450901) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450900) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450907) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450906) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450905) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450904) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450895) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450894) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450893) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450892) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450899) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450898) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450897) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450896) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450887) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450886) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450885) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450884) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450891) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450890) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450889) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450888) 248
        /\ L5.defined M' ((V 50%nat) + 8) 504).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G18 G19 G20 G21 G23 G24 G25 pvzI6 K1 K2 pvzI7 K4 K5 K6 K7 K8 K9 pvzI8 K11 K12 K13 K14 K15 K16 K17 K18.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV50l; move HV50l before pvzI4; pose proof (proj2 pvzI4) as HV50r; move HV50r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV51l; move HV51l before pvzI5; pose proof (proj2 pvzI5) as HV51r; move HV51r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K10l; move K10l before pvzI8; pose proof (proj2 pvzI8) as K10r; move K10r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PafnT.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PafnT.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PafnT.kn0).
  { unfold know_ok, PafnT.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K10l K10r K12 K13 K15 K18; lia | clear - HV51l HV51r K10l K10r K12 K13 K15 K18; lia | clear - HV51l HV51r K10l K10r K12 K13 K15 K18; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PafnT.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PafnT.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 8) -> ~ ((((vz_50 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 0) + 64) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PafnT.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PafnT.ps0) with 0x7b90c in Hms. change (SR.ps_regs PafnT.ps0) with (map (fun i => (i, nth i PafnT.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PafnT.ps0) with PafnT.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PafnT.regs0 PafnT.regs_out0 80 KS_afnT KS_afnT_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PafnT.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PafnT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafnT.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PafnT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafnT.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PafnT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 23%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 24%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 25%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 26%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 27%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 28%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 29%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 30%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 31%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 32%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 33%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PafnZ := LibSegBa_afnZ_b.
Definition KS_afnZ : list nat := Eval vm_compute in (BG.kept_list 80 PafnZ.regs0 PafnZ.regs_out0).
Lemma KS_afnZ_ok : BG.kept_ok 80 PafnZ.regs0 PafnZ.regs_out0 KS_afnZ = true. Proof. vm_compute. reflexivity. Qed.
Lemma afnZ_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 21) = Z_to_bv 64 (V 35%nat) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6905856 <= (V 50%nat) <= 140737488354816 ->
  aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 512 -> L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) ->
  L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 50%nat) + 504) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 512 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 128) + 128 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 128)) ->
  (65536 + 6840320 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) -> (65536 + 6840320 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= 65536) -> (65536 + 6840320 <= (V 51%nat) \/ (V 51%nat) + 1 <= 65536) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 71%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 51%nat) + 0) <= bv_unsigned a < ((V 51%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 51%nat) + 0) <= i < ((V 51%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb657c M) (st fx' R' 0xb6694 M')
        /\ (forall x, In x KS_afnZ -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 60%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 61%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 62%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 63%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 69%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 70%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 71%nat)
        /\ L5.u8_at RSEGS M' (V 51%nat) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 G2 G8 G19 G21 pvzI18 K1 K2 pvzI19 K4 K5 K6 K7 K8 K9 pvzI20 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV35l; move HV35l before pvzI2; pose proof (proj2 pvzI2) as HV35r; move HV35r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV50l; move HV50l before pvzI3; pose proof (proj2 pvzI3) as HV50r; move HV50r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV51l; move HV51l before pvzI4; pose proof (proj2 pvzI4) as HV51r; move HV51r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV60l; move HV60l before pvzI5; pose proof (proj2 pvzI5) as HV60r; move HV60r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV61l; move HV61l before pvzI6; pose proof (proj2 pvzI6) as HV61r; move HV61r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV62l; move HV62l before pvzI7; pose proof (proj2 pvzI7) as HV62r; move HV62r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV63l; move HV63l before pvzI8; pose proof (proj2 pvzI8) as HV63r; move HV63r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV64l; move HV64l before pvzI9; pose proof (proj2 pvzI9) as HV64r; move HV64r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV65l; move HV65l before pvzI10; pose proof (proj2 pvzI10) as HV65r; move HV65r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV66l; move HV66l before pvzI11; pose proof (proj2 pvzI11) as HV66r; move HV66r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV67l; move HV67l before pvzI12; pose proof (proj2 pvzI12) as HV67r; move HV67r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV68l; move HV68l before pvzI13; pose proof (proj2 pvzI13) as HV68r; move HV68r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV69l; move HV69l before pvzI14; pose proof (proj2 pvzI14) as HV69r; move HV69r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV70l; move HV70l before pvzI15; pose proof (proj2 pvzI15) as HV70r; move HV70r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV71l; move HV71l before pvzI16; pose proof (proj2 pvzI16) as HV71r; move HV71r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV72l; move HV72l before pvzI17; pose proof (proj2 pvzI17) as HV72r; move HV72r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K0l; move K0l before pvzI18; pose proof (proj2 pvzI18) as K0r; move K0r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K3l; move K3l before pvzI19; pose proof (proj2 pvzI19) as K3r; move K3r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K10l; move K10l before pvzI20; pose proof (proj2 pvzI20) as K10r; move K10r before pvzI20; clear pvzI20.
  set (vz_2 := V 2%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 35%nat => Z_to_bv 64 vz_35 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 35%nat => vz_35 | 50%nat => vz_50 | 51%nat => vz_51 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 73%nat. }
  assert (HR: regs_ok E PafnZ.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PafnZ.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PafnZ.kn0).
  { unfold know_ok, PafnZ.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K10l K10r K12 K13 K15 K18; lia | clear - HV51l HV51r K10l K10r K12 K13 K15 K18; lia | clear - HV51l HV51r K10l K10r K12 K13 K15 K18; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV61l HV61r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV63l HV63r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K30]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PafnZ.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PafnZ.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_51 + 0) <= bv_unsigned a < (vz_51 + 0) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PafnZ.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV51l HV51r K10l K10r K12 K13 K15 K18 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PafnZ.ps0) with 0xb6694 in Hms. change (SR.ps_regs PafnZ.ps0) with (map (fun i => (i, nth i PafnZ.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PafnZ.ps0) with PafnZ.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PafnZ.regs0 PafnZ.regs_out0 80 KS_afnZ KS_afnZ_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PafnZ.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PafnZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafnZ.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PafnZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafnZ.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PafnZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafnZ.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PafnZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafnZ.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PafnZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafnZ.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PafnZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafnZ.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PafnZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafnZ.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PafnZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafnZ.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PafnZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafnZ.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PafnZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafnZ.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PafnZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafnZ.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PafnZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafnZ.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PafnZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PafnZ.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PafnZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

End PNAFIP.
