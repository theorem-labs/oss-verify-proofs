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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require LibSegBa_adkA_b LibSegBa_adkB1_b LibSegBa_adkG1_b LibSegBa_adkG2_b LibSegBa_adkB2_b LibSegBa_adkC_b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNADP1.
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
Module PadkA := LibSegBa_adkA_b.
Definition KS_adkA : list nat := Eval vm_compute in (BG.kept_list 80 PadkA.regs0 PadkA.regs_out0).
Lemma KS_adkA_ok : BG.kept_ok 80 PadkA.regs0 PadkA.regs_out0 KS_adkA = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 ((V 33%nat) + 42) -> getr R (reg 12) = Z_to_bv 64 (V 34%nat) ->
  L5.img_clear M 1249280 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 256) <= bv_unsigned a < ((V 2%nat) - 256) + 256) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 256) <= i < ((V 2%nat) - 256) + 256) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3e24 M) (st fx' R' 0x5df30 M')
        /\ (forall x, In x KS_adkA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 736924
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 256)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 256)
        /\ getr R' (reg 10) = Z_to_bv 64 320
        /\ getr R' (reg 11) = Z_to_bv 64 1309752
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 19) = Z_to_bv 64 2147450880
        /\ getr R' (reg 20) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 22) = getr R (reg 22)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 27) = getr R (reg 27)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (bv_unsigned (getr R (reg 27)))
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) (bv_unsigned (Z_to_bv 64 ((V 33%nat) + 42)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G10 G11 G12 K0 K1 K2 pvzI4 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K3l; move K3l before pvzI4; pose proof (proj2 pvzI4) as K3r; move K3r before pvzI4; clear pvzI4.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 35%nat. }
  assert (HR: regs_ok E PadkA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadkA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadkA.kn0).
  { unfold know_ok, PadkA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadkA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadkA.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 256) <= bv_unsigned a < (vz_2 - 256) + 256) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PadkA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PadkA.ps0) with 0x5df30 in Hms. change (SR.ps_regs PadkA.ps0) with (map (fun i => (i, nth i PadkA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PadkA.ps0) with PadkA.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkA.regs0 PadkA.regs_out0 80 KS_adkA KS_adkA_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PadkA.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PadkA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkA.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PadkA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkA.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PadkA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkA.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PadkA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkA.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkA.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PadkA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkA.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PadkA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkA.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PadkA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkA.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PadkA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkA.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PadkA.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PadkA.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PadkA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkA.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PadkA.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
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
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | f_equal; first [reflexivity | wordP' ZA Hag] | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadkB1 := LibSegBa_adkB1_b.
Definition KS_adkB1 : list nat := Eval vm_compute in (BG.kept_list 80 PadkB1.regs0 PadkB1.regs_out0).
Lemma KS_adkB1_ok : BG.kept_ok 80 PadkB1.regs0 PadkB1.regs_out0 KS_adkB1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkB1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 10) = Z_to_bv 64 (V 50%nat) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 24) = Z_to_bv 64 (V 34%nat) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 4096 <= (V 50%nat) <= 140737488354816 ->
  aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 512 -> L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) ->
  L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 50%nat) + 504) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 512 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 256) + 256 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 256)) -> (((V 2%nat) - 256) + 256 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 256)) ->
  (65536 + 6840320 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) -> (65536 + 6840320 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= 65536) -> (65536 + 6840320 <= (V 51%nat) \/ (V 51%nat) + 1 <= 65536) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 144) <= bv_unsigned a < ((V 2%nat) - 144) + 8) -> ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 24) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 40) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 144) <= i < ((V 2%nat) - 144) + 8) -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 24) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 40) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3e9c M) (st fx' R' 0xb3fac M')
        /\ (forall x, In x KS_adkB1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 18446744073709551608
        /\ getr R' (reg 11) = Z_to_bv 64 18446744073709551602
        /\ getr R' (reg 12) = Z_to_bv 64 18446744073709551603
        /\ getr R' (reg 13) = Z_to_bv 64 736804
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 50%nat) / 8)
        /\ getr R' (reg 15) = Z_to_bv 64 18446744073709551601
        /\ getr R' (reg 18) = getr R (reg 18)
        /\ getr R' (reg 19) = Z_to_bv 64 2147450880
        /\ getr R' (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 50%nat)
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450915) 243
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450914) 243
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450913) 243
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450912) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450919) 243
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450918) 243
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450917) 243
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450916) 243
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450911) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450910) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450909) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450908) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450907) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450906) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450905) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450904) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450899) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450898) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450897) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450896) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450903) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450902) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450901) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450900) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450891) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450890) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450889) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450888) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450895) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450894) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450893) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450892) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450887) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450886) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450885) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450884) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450883) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450882) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450881) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450880) 241
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 16) 736804
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 8) 71165
        /\ L5.u64_at RSEGS M' (V 50%nat) 1102416563
        /\ L5.defined M' ((V 50%nat) + 24) 488
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 50%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G19 G20 G24 pvzI6 K1 K2 pvzI7 K4 K5 K6 K7 K8 K9 pvzI8 K11 K12 K13 K14 K15 K16 K17 K18.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV50l; move HV50l before pvzI4; pose proof (proj2 pvzI4) as HV50r; move HV50r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV51l; move HV51l before pvzI5; pose proof (proj2 pvzI5) as HV51r; move HV51r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K10l; move K10l before pvzI8; pose proof (proj2 pvzI8) as K10r; move K10r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PadkB1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadkB1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadkB1.kn0).
  { unfold know_ok, PadkB1.kn0.
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
  pvz_hg ltac:(idtac; destruct (PadkB1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadkB1.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 144) <= bv_unsigned a < (vz_2 - 144) + 8) -> ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 24) -> ~ ((((vz_50 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 0) + 40) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PadkB1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K14 K15 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PadkB1.ps0) with 0xb3fac in Hms. change (SR.ps_regs PadkB1.ps0) with (map (fun i => (i, nth i PadkB1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PadkB1.ps0) with PadkB1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkB1.regs0 PadkB1.regs_out0 80 KS_adkB1 KS_adkB1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PadkB1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkB1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkB1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PadkB1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkB1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PadkB1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkB1.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PadkB1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkB1.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PadkB1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkB1.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PadkB1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkB1.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PadkB1.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PadkB1.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PadkB1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkB1.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PadkB1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkB1.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PadkB1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkB1.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PadkB1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
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
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 33%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 34%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 35%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 36%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 37%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 38%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 39%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 40%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 41%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 42%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 44%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 43%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadkG1 := LibSegBa_adkG1_b.
Definition KS_adkG1_0 : list nat := Eval vm_compute in (BG.kept_list 80 PadkG1.regs0 PadkG1.regs_out0).
Lemma KS_adkG1_0_ok : BG.kept_ok 80 PadkG1.regs0 PadkG1.regs_out0 KS_adkG1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_adkG1_1 : list nat := Eval vm_compute in (BG.kept_list 80 PadkG1.regs0 PadkG1.regs_out1).
Lemma KS_adkG1_1_ok : BG.kept_ok 80 PadkG1.regs0 PadkG1.regs_out1 KS_adkG1_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkG1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (V 34%nat) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5.u8_at RSEGS M 6759136 (V 46%nat) ->
  0 <= (V 46%nat) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb3fac M) (st fx' R' 0xb3fbc M')
        /\ (forall x, In x KS_adkG1_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 46%nat)
        /\ 1 <= (((V 46%nat) - 0) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xb3fac M) (st fx' R' 0xb4b08 M')
        /\ (forall x, In x KS_adkG1_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 46%nat)
        /\ (((V 46%nat) - 0) mod 2 ^ 64) < 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G19 G20 G23 G24 G26 G27 pvzI6 K1 K2 K3 pvzI7.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV46l; move HV46l before pvzI4; pose proof (proj2 pvzI4) as HV46r; move HV46r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K4l; move K4l before pvzI7; pose proof (proj2 pvzI7) as K4r; move K4r before pvzI7; clear pvzI7.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 46%nat => Z_to_bv 64 vz_46 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 46%nat => vz_46 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PadkG1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadkG1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadkG1.kn0).
  { unfold know_ok, PadkG1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV46l HV46r K4l K4r) | clear; lia | clear; lia | byte_tac ltac:(clear - HV46l HV46r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadkG1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadkG1.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PadkG1.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PadkG1.ps0) with 0xb3fbc in Hms. change (SR.ps_regs PadkG1.ps0) with (map (fun i => (i, nth i PadkG1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PadkG1.ps0) with PadkG1.cells0 in Hcells. unfold PadkG1.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkG1.regs0 PadkG1.regs_out0 80 KS_adkG1_0 KS_adkG1_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PadkG1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. 
    change (SR.ps_pc PadkG1.ps1) with 0xb4b08 in Hms. change (SR.ps_regs PadkG1.ps1) with (map (fun i => (i, nth i PadkG1.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PadkG1.ps1) with PadkG1.cells1 in Hcells. unfold PadkG1.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkG1.regs0 PadkG1.regs_out1 80 KS_adkG1_1 KS_adkG1_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PadkG1.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkG1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadkG2 := LibSegBa_adkG2_b.
Definition KS_adkG2_0 : list nat := Eval vm_compute in (BG.kept_list 80 PadkG2.regs0 PadkG2.regs_out0).
Lemma KS_adkG2_0_ok : BG.kept_ok 80 PadkG2.regs0 PadkG2.regs_out0 KS_adkG2_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_adkG2_1 : list nat := Eval vm_compute in (BG.kept_list 80 PadkG2.regs0 PadkG2.regs_out1).
Lemma KS_adkG2_1_ok : BG.kept_ok 80 PadkG2.regs0 PadkG2.regs_out1 KS_adkG2_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkG2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (V 34%nat) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5.u8_at RSEGS M 6759168 (V 46%nat) ->
  0 <= (V 46%nat) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb3fbc M) (st fx' R' 0xb3fcc M')
        /\ (forall x, In x KS_adkG2_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 46%nat)
        /\ 1 <= (((V 46%nat) - 0) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xb3fbc M) (st fx' R' 0xb4b5c M')
        /\ (forall x, In x KS_adkG2_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 46%nat)
        /\ (((V 46%nat) - 0) mod 2 ^ 64) < 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G19 G20 G23 G24 G26 G27 pvzI6 K1 K2 K3 pvzI7.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV46l; move HV46l before pvzI4; pose proof (proj2 pvzI4) as HV46r; move HV46r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K4l; move K4l before pvzI7; pose proof (proj2 pvzI7) as K4r; move K4r before pvzI7; clear pvzI7.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 46%nat => Z_to_bv 64 vz_46 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 46%nat => vz_46 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PadkG2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadkG2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadkG2.kn0).
  { unfold know_ok, PadkG2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV46l HV46r K4l K4r) | clear; lia | clear; lia | byte_tac ltac:(clear - HV46l HV46r K4l K4r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadkG2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadkG2.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PadkG2.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PadkG2.ps0) with 0xb3fcc in Hms. change (SR.ps_regs PadkG2.ps0) with (map (fun i => (i, nth i PadkG2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PadkG2.ps0) with PadkG2.cells0 in Hcells. unfold PadkG2.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkG2.regs0 PadkG2.regs_out0 80 KS_adkG2_0 KS_adkG2_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PadkG2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. 
    change (SR.ps_pc PadkG2.ps1) with 0xb4b5c in Hms. change (SR.ps_regs PadkG2.ps1) with (map (fun i => (i, nth i PadkG2.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PadkG2.ps1) with PadkG2.cells1 in Hcells. unfold PadkG2.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkG2.regs0 PadkG2.regs_out1 80 KS_adkG2_1 KS_adkG2_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PadkG2.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkG2.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadkB2 := LibSegBa_adkB2_b.
Definition KS_adkB2 : list nat := Eval vm_compute in (BG.kept_list 80 PadkB2.regs0 PadkB2.regs_out0).
Lemma KS_adkB2_ok : BG.kept_ok 80 PadkB2.regs0 PadkB2.regs_out0 KS_adkB2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkB2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (V 34%nat) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 4096 <= (V 50%nat) <= 140737488354816 ->
  aligned (V 50%nat) 32 -> L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) -> (((V 2%nat) - 256) + 256 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 256)) ->
  (65536 + 6840320 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 64 -> (65536 + 6840320 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= 65536) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((((V 50%nat) / 8) + 2147450880) + 4) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 4) + 18) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((((V 50%nat) / 8) + 2147450880) + 4) <= i < ((((V 50%nat) / 8) + 2147450880) + 4) + 18) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3fcc M) (st fx' R' 0x78130 M')
        /\ (forall x, In x KS_adkB2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 737320
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 50%nat) + 32)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 144
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 50%nat) + 32)
        /\ getr R' (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880)
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450901) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450900) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450895) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450894) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450893) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450892) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450899) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450898) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450897) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450896) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450887) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450886) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450885) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450884) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450891) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450890) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450889) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450888) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G19 G20 G23 G24 G26 G27 pvzI5 K1 K2 pvzI6 K4 K5 K6 K7 K8 K9 K10.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV50l; move HV50l before pvzI4; pose proof (proj2 pvzI4) as HV50r; move HV50r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PadkB2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadkB2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadkB2.kn0).
  { unfold know_ok, PadkB2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8 K10) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8 K10) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8 K10) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K6 K7 K8 K10; lia | clear - HV50l HV50r K3l K3r K6 K7 K8 K10; lia | clear - HV50l HV50r K3l K3r K6 K7 K8 K10; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8 K10) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8 K10) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8 K10) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8 K10) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K6 K7 K8 K10; lia | clear - HV50l HV50r K3l K3r K6 K7 K8 K10; lia | clear - HV50l HV50r K3l K3r K6 K7 K8 K10; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8 K10) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadkB2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadkB2.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((vz_50 / 8) + 2147450880) + 4) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 4) + 18) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PadkB2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8 K10) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K3l K3r K6 K7 K8 K10 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PadkB2.ps0) with 0x78130 in Hms. change (SR.ps_regs PadkB2.ps0) with (map (fun i => (i, nth i PadkB2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PadkB2.ps0) with PadkB2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkB2.regs0 PadkB2.regs_out0 80 KS_adkB2 KS_adkB2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PadkB2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PadkB2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkB2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkB2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkB2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PadkB2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkB2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PadkB2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkB2.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PadkB2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkB2.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PadkB2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8 K10) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8 K10) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8 K10) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8 K10) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8 K10) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8 K10) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8 K10) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8 K10) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8 K10) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8 K10) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8 K10) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8 K10) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8 K10) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8 K10) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8 K10) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8 K10) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8 K10) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K6 K7 K8 K10) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadkC := LibSegBa_adkC_b.
Definition KS_adkC_0 : list nat := Eval vm_compute in (BG.kept_list 80 PadkC.regs0 PadkC.regs_out0).
Lemma KS_adkC_0_ok : BG.kept_ok 80 PadkC.regs0 PadkC.regs_out0 KS_adkC_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_adkC_1 : list nat := Eval vm_compute in (BG.kept_list 80 PadkC.regs0 PadkC.regs_out1).
Lemma KS_adkC_1_ok : BG.kept_ok 80 PadkC.regs0 PadkC.regs_out1 KS_adkC_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkC_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 18) = Z_to_bv 64 ((V 50%nat) + 32) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (V 34%nat) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 6905856 <= (V 34%nat) <= 140737488355312 ->
  aligned (V 34%nat) 8 -> (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 2 -> L5.u64_at RSEGS M (V 34%nat) (V 35%nat) ->
  L5.u64_at RSEGS M ((V 34%nat) + 8) (V 36%nat) -> (((V 2%nat) - 256) + 256 <= (V 34%nat) \/ (V 34%nat) + 16 <= ((V 2%nat) - 256)) -> 4096 <= (V 33%nat) <= 140737488355280 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 48 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 6 -> L5.writable RSEGS M (V 33%nat) 42 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 48 <= ((V 2%nat) - 256)) ->
  (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 48 <= 65536) -> 4096 <= (V 50%nat) <= 140737488354816 -> ((V 33%nat) + 48 <= (V 34%nat) \/ (V 34%nat) + 16 <= (V 33%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb4028 M) (st fx' R' 0xb406c M')
        /\ (forall x, In x KS_adkC_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 34%nat) + 8)
        /\ getr R' (reg 11) = Z_to_bv 64 ((((V 34%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 30) = Z_to_bv 64 (V 33%nat))
      \/ (msteps RSEGS (st fx R 0xb4028 M) (st fx' R' 0xb406c M')
        /\ (forall x, In x KS_adkC_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 34%nat) + 8)
        /\ getr R' (reg 11) = Z_to_bv 64 ((((V 34%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 12) = Z_to_bv 64 45
        /\ getr R' (reg 30) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ L5.u8_at RSEGS M' (V 33%nat) 45)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G18 G19 G20 G23 G24 G26 G27 pvzI7 K1 K2 pvzI8 K4 K5 K6 K7 K8 K9 pvzI9 K11 K12 K13 K14 K15 K16 pvzI10 K18.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV50l; move HV50l before pvzI6; pose proof (proj2 pvzI6) as HV50r; move HV50r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K10l; move K10l before pvzI9; pose proof (proj2 pvzI9) as K10r; move K10r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K17l; move K17l before pvzI10; pose proof (proj2 pvzI10) as K17r; move K17r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PadkC.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadkC.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadkC.kn0).
  { unfold know_ok, PadkC.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9 K15) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9 K15) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9 K15) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K9 K15; lia | clear - HV2l HV2r K0l K0r K9 K15; lia | clear - HV2l HV2r K0l K0r K9 K15; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5 K9 K18) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5 K9 K18) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5 K9 K18) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5 K9 K18) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K3l K3r K5 K9 K18; lia | clear - HV34l HV34r K3l K3r K5 K9 K18; lia | clear - HV34l HV34r K3l K3r K5 K9 K18; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5 K9 K18) | evalEk ZA ltac:(clear - HV35l HV35r) | clear - HV34l HV34r K3l K3r K5 K9 K18; lia | clear - HV34l HV34r K3l K3r K5 K9 K18; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5 K9 K18) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV34l HV34r K3l K3r K5 K9 K18; lia | clear - HV34l HV34r K3l K3r K5 K9 K18; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5 K9 K18) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K12 K15 K16 K18) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K12 K15 K16 K18) | clear; lia | exact K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K12 K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K12 K15 K16 K18) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K10l K10r K12 K15 K16 K18; lia | clear - HV33l HV33r K10l K10r K12 K15 K16 K18; lia | clear - HV33l HV33r K10l K10r K12 K15 K16 K18; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K12 K15 K16 K18) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K10l K10r K12 K15 K16 K18; lia | clear - HV33l HV33r K10l K10r K12 K15 K16 K18; lia | clear - HV33l HV33r K10l K10r K12 K15 K16 K18; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K12 K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K12 K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K12 K15 K16 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5 K9 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadkC.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadkC.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_33 + 0) <= bv_unsigned a < (vz_33 + 0) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PadkC.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K10l K10r K12 K15 K16 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K10l K10r K12 K15 K16 K18 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PadkC.ps0) with 0xb406c in Hms. change (SR.ps_regs PadkC.ps0) with (map (fun i => (i, nth i PadkC.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PadkC.ps0) with PadkC.cells0 in Hcells. unfold PadkC.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkC.regs0 PadkC.regs_out0 80 KS_adkC_0 KS_adkC_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PadkC.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkC.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PadkC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkC.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PadkC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PadkC.regs_out0 E' R' 30 Hregs) by (clear; lia). cbn [nth PadkC.regs_out0]. first [reflexivity | wordP' ZA Hag].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. 
    change (SR.ps_pc PadkC.ps1) with 0xb406c in Hms. change (SR.ps_regs PadkC.ps1) with (map (fun i => (i, nth i PadkC.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PadkC.ps1) with PadkC.cells1 in Hcells. unfold PadkC.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkC.regs0 PadkC.regs_out1 80 KS_adkC_1 KS_adkC_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PadkC.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkC.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkC.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PadkC.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkC.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PadkC.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkC.regs_out1 E' R' 30 Hregs) by (clear; lia). cbn [nth PadkC.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K10l K10r K12 K15 K16 K18) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.
(* [comment removed for export] *)

End PNADP1.
