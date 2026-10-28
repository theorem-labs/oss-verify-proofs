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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require LibSegBa_awvA_b LibSegBa_awvB_b LibSegBa_awvR2_b LibSegBa_awvJ1_b LibSegBa_awvJ2_b LibSegBa_awvJ3_b LibSegBa_awvJ4_b LibSegBa_awvJ5_b LibSegBa_awvJ6_b LibSegBa_awvJ7_b LibSegBa_awvJ8_b LibSegBa_awvJ9_b LibSegBa_awvJ10_b LibSegBa_awvJ11_b LibSegBa_awvJ12_b LibSegBa_awvJ13_b LibSegBa_awvJ14_b LibSegBa_awvJ15_b LibSegBa_awvJ16_b LibSegBa_awvJ17_b LibSegBa_awvJ18_b LibSegBa_awvJ19_b LibSegBa_awvJ127_b LibSegBa_awvJ255_b LibSegBa_awvJ0_b LibSegBa_awvJr1_b LibSegBa_awvJr2_b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNARVTP.
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
Module PawvA := LibSegBa_awvA_b.
Definition KS_awvA : list nat := Eval vm_compute in (BG.kept_list 80 PawvA.regs0 PawvA.regs_out0).
Lemma KS_awvA_ok : BG.kept_ok 80 PawvA.regs0 PawvA.regs_out0 KS_awvA = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) -> getr R (reg 13) = Z_to_bv 64 (V 36%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 160) <= bv_unsigned a < ((V 2%nat) - 160) + 160) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 160) <= i < ((V 2%nat) - 160) + 160) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xaff88 M) (st fx' R' 0x5df30 M')
        /\ (forall x, In x KS_awvA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 720900
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 160)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 160)
        /\ getr R' (reg 10) = Z_to_bv 64 480
        /\ getr R' (reg 11) = Z_to_bv 64 1309752
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 20) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 2147450880
        /\ getr R' (reg 22) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 36%nat)
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G10 G11 G12 G13 K0 K1 K2 pvzI6 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PawvA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvA.kn0).
  { unfold know_ok, PawvA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvA.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 160) <= bv_unsigned a < (vz_2 - 160) + 160) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PawvA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvA.ps0) with 0x5df30 in Hms. change (SR.ps_regs PawvA.ps0) with (map (fun i => (i, nth i PawvA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvA.ps0) with PawvA.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvA.regs0 PawvA.regs_out0 80 KS_awvA KS_awvA_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvA.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PawvA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvA.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PawvA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvA.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PawvA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvA.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PawvA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvA.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvA.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvA.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PawvA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvA.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PawvA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvA.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PawvA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvA.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PawvA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvA.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PawvA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvA.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PawvA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
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
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvB := LibSegBa_awvB_b.
Definition KS_awvB : list nat := Eval vm_compute in (BG.kept_list 80 PawvB.regs0 PawvB.regs_out0).
Lemma KS_awvB_ok : BG.kept_ok 80 PawvB.regs0 PawvB.regs_out0 KS_awvB = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 (V 35%nat) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) ->
  140735332487392 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 -> 6905856 <= (V 50%nat) <= 140737488354816 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 512 ->
  L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 50%nat) + 504) (V 51%nat) ->
  4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 512 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) ->
  (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> (65536 + 6840320 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) -> (65536 + 6840320 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= 65536) ->
  (65536 + 6840320 <= (V 51%nat) \/ (V 51%nat) + 1 <= 65536) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 8) -> ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 24) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 8) -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 24) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb0004 M) (st fx' R' 0xb016c M')
        /\ (forall x, In x KS_awvB -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 18
        /\ getr R' (reg 11) = Z_to_bv 64 18446744073709551608
        /\ getr R' (reg 12) = Z_to_bv 64 18446744073709551603
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 35%nat) - 1)
        /\ getr R' (reg 14) = Z_to_bv 64 108821
        /\ getr R' (reg 15) = Z_to_bv 64 720776
        /\ getr R' (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 50%nat)
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450939) 243
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450938) 243
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450937) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450936) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450931) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450930) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450929) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450928) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450935) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450934) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450933) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450932) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450923) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450922) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450921) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450920) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450927) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450926) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450925) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450924) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450915) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450914) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450913) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450912) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450919) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450918) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450917) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450916) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450907) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450906) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450905) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450904) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450911) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450910) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450909) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450908) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450899) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450898) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450897) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450896) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450903) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450902) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450901) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450900) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450891) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450890) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450889) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450888) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450895) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450894) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450893) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450892) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450887) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450886) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450885) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450884) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450883) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450882) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450881) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450880) 241
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 16) 720776
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 8) 108821
        /\ L5.u64_at RSEGS M' (V 50%nat) 1102416563
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) (V 50%nat)
        /\ L5.defined M' ((V 50%nat) + 24) 488).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G20 G21 G22 G23 G26 pvzI8 K1 K2 pvzI9 K4 pvzI10 K6 K7 K8 K9 K10 K11 pvzI11 K13 K14 K15 K16 K17 K18 K19 K20.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV50l; move HV50l before pvzI6; pose proof (proj2 pvzI6) as HV50r; move HV50r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV51l; move HV51l before pvzI7; pose proof (proj2 pvzI7) as HV51r; move HV51r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K5l; move K5l before pvzI10; pose proof (proj2 pvzI10) as K5r; move K5r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K12l; move K12l before pvzI11; pose proof (proj2 pvzI11) as K12r; move K12r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PawvB.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvB.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvB.kn0).
  { unfold know_ok, PawvB.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K17) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K17) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K17) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K17; lia | clear - HV2l HV2r K0l K0r K16 K17; lia | clear - HV2l HV2r K0l K0r K16 K17; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | clear; lia | exact K6]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19; lia | clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19; lia | clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19; lia | clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19; lia | clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19; lia | clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19; lia | clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk ZA ltac:(clear - HV51l HV51r K12l K12r K14 K15 K17 K20) | clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19; lia | clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K12l K12r K14 K15 K17 K20) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K12l K12r K14 K15 K17 K20) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K12l K12r K14 K15 K17 K20; lia | clear - HV51l HV51r K12l K12r K14 K15 K17 K20; lia | clear - HV51l HV51r K12l K12r K14 K15 K17 K20; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K12l K12r K14 K15 K17 K20) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K12l K12r K14 K15 K17 K20) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K12l K12r K14 K15 K17 K20) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K12l K12r K14 K15 K17 K20) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvB.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvB.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 128) <= bv_unsigned a < (vz_2 - 128) + 8) -> ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 24) -> ~ ((((vz_50 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 0) + 64) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PawvB.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K17 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvB.ps0) with 0xb016c in Hms. change (SR.ps_regs PawvB.ps0) with (map (fun i => (i, nth i PawvB.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvB.ps0) with PawvB.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvB.regs0 PawvB.regs_out0 80 KS_awvB KS_awvB_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvB.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvB.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvB.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PawvB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvB.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PawvB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvB.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PawvB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvB.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PawvB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvB.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PawvB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvB.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PawvB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvB.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PawvB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 23%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 24%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 25%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 26%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 27%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 28%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 29%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 30%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 31%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 32%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 33%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 34%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 35%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 36%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 37%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 38%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 39%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 40%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 41%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 42%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 43%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 44%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 45%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 46%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 47%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 48%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 49%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 50%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 51%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 52%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 53%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 54%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 55%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 56%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 57%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 58%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 59%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 60%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 61%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 62%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 63%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K17) | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 64%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16 K18 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvR2 := LibSegBa_awvR2_b.
Definition KS_awvR2 : list nat := Eval vm_compute in (BG.kept_list 80 PawvR2.regs0 PawvR2.regs_out0).
Lemma KS_awvR2_ok : BG.kept_ok 80 PawvR2.regs0 PawvR2.regs_out0 KS_awvR2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvR2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) ->
  140735332487392 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 50%nat) <= 140737488354816 ->
  aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 512 -> L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) ->
  L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 50%nat) + 504) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 512 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) ->
  (65536 + 6840320 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) -> (65536 + 6840320 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= 65536) -> (65536 + 6840320 <= (V 51%nat) \/ (V 51%nat) + 1 <= 65536) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 72%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 51%nat) + 0) <= bv_unsigned a < ((V 51%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 51%nat) + 0) <= i < ((V 51%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1440 M) (st fx' R' 0xb1578 M')
        /\ (forall x, In x KS_awvR2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 60%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 61%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 62%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 63%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 69%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 70%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 71%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 72%nat)
        /\ L5.u8_at RSEGS M' (V 51%nat) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 G2 G8 G19 pvzI17 K1 K2 pvzI18 K4 K5 K6 K7 K8 K9 pvzI19 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV50l; move HV50l before pvzI2; pose proof (proj2 pvzI2) as HV50r; move HV50r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV51l; move HV51l before pvzI3; pose proof (proj2 pvzI3) as HV51r; move HV51r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV60l; move HV60l before pvzI4; pose proof (proj2 pvzI4) as HV60r; move HV60r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV61l; move HV61l before pvzI5; pose proof (proj2 pvzI5) as HV61r; move HV61r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV62l; move HV62l before pvzI6; pose proof (proj2 pvzI6) as HV62r; move HV62r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV63l; move HV63l before pvzI7; pose proof (proj2 pvzI7) as HV63r; move HV63r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV64l; move HV64l before pvzI8; pose proof (proj2 pvzI8) as HV64r; move HV64r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV65l; move HV65l before pvzI9; pose proof (proj2 pvzI9) as HV65r; move HV65r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV66l; move HV66l before pvzI10; pose proof (proj2 pvzI10) as HV66r; move HV66r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV67l; move HV67l before pvzI11; pose proof (proj2 pvzI11) as HV67r; move HV67r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV68l; move HV68l before pvzI12; pose proof (proj2 pvzI12) as HV68r; move HV68r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV69l; move HV69l before pvzI13; pose proof (proj2 pvzI13) as HV69r; move HV69r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV70l; move HV70l before pvzI14; pose proof (proj2 pvzI14) as HV70r; move HV70r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV71l; move HV71l before pvzI15; pose proof (proj2 pvzI15) as HV71r; move HV71r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV72l; move HV72l before pvzI16; pose proof (proj2 pvzI16) as HV72r; move HV72r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K0l; move K0l before pvzI17; pose proof (proj2 pvzI17) as K0r; move K0r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K3l; move K3l before pvzI18; pose proof (proj2 pvzI18) as K3r; move K3r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K10l; move K10l before pvzI19; pose proof (proj2 pvzI19) as K10r; move K10r before pvzI19; clear pvzI19.
  set (vz_2 := V 2%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 50%nat => vz_50 | 51%nat => vz_51 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 73%nat. }
  assert (HR: regs_ok E PawvR2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvR2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvR2.kn0).
  { unfold know_ok, PawvR2.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K31]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvR2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvR2.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_51 + 0) <= bv_unsigned a < (vz_51 + 0) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PawvR2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV51l HV51r K10l K10r K12 K13 K15 K18 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvR2.ps0) with 0xb1578 in Hms. change (SR.ps_regs PawvR2.ps0) with (map (fun i => (i, nth i PawvR2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvR2.ps0) with PawvR2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvR2.regs0 PawvR2.regs_out0 80 KS_awvR2 KS_awvR2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvR2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PawvR2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvR2.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PawvR2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvR2.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PawvR2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvR2.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PawvR2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvR2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvR2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvR2.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PawvR2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvR2.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PawvR2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvR2.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PawvR2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvR2.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PawvR2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvR2.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PawvR2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvR2.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PawvR2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvR2.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PawvR2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvR2.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PawvR2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvR2.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PawvR2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvR2.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PawvR2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15 K18) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvJ1 := LibSegBa_awvJ1_b.
Definition KS_awvJ1 : list nat := Eval vm_compute in (BG.kept_list 80 PawvJ1.regs0 PawvJ1.regs_out0).
Lemma KS_awvJ1_ok : BG.kept_ok 80 PawvJ1.regs0 PawvJ1.regs_out0 KS_awvJ1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvJ1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 18 -> getr R (reg 13) = Z_to_bv 64 0 -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 1 -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb016c M) (st fx' R' 0xb018c M')
        /\ (forall x, In x KS_awvJ1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 721292
        /\ getr R' (reg 11) = Z_to_bv 64 577956
        /\ getr R' (reg 13) = Z_to_bv 64 143336).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G13 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI6 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PawvJ1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvJ1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvJ1.kn0).
  { unfold know_ok, PawvJ1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvJ1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvJ1.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PawvJ1.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvJ1.ps0) with 0xb018c in Hms. change (SR.ps_regs PawvJ1.ps0) with (map (fun i => (i, nth i PawvJ1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvJ1.ps0) with PawvJ1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvJ1.regs0 PawvJ1.regs_out0 80 KS_awvJ1 KS_awvJ1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvJ1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvJ1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvJ1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvJ1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PawvJ1.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PawvJ1.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvJ2 := LibSegBa_awvJ2_b.
Definition KS_awvJ2 : list nat := Eval vm_compute in (BG.kept_list 80 PawvJ2.regs0 PawvJ2.regs_out0).
Lemma KS_awvJ2_ok : BG.kept_ok 80 PawvJ2.regs0 PawvJ2.regs_out0 KS_awvJ2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvJ2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 18 -> getr R (reg 13) = Z_to_bv 64 1 -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 2 -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb016c M) (st fx' R' 0xb02c4 M')
        /\ (forall x, In x KS_awvJ2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 721604
        /\ getr R' (reg 11) = Z_to_bv 64 578268
        /\ getr R' (reg 13) = Z_to_bv 64 143340).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G13 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI6 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PawvJ2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvJ2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvJ2.kn0).
  { unfold know_ok, PawvJ2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvJ2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvJ2.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PawvJ2.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvJ2.ps0) with 0xb02c4 in Hms. change (SR.ps_regs PawvJ2.ps0) with (map (fun i => (i, nth i PawvJ2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvJ2.ps0) with PawvJ2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvJ2.regs0 PawvJ2.regs_out0 80 KS_awvJ2 KS_awvJ2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvJ2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvJ2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvJ2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvJ2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PawvJ2.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PawvJ2.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvJ3 := LibSegBa_awvJ3_b.
Definition KS_awvJ3 : list nat := Eval vm_compute in (BG.kept_list 80 PawvJ3.regs0 PawvJ3.regs_out0).
Lemma KS_awvJ3_ok : BG.kept_ok 80 PawvJ3.regs0 PawvJ3.regs_out0 KS_awvJ3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvJ3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 18 -> getr R (reg 13) = Z_to_bv 64 2 -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 3 -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb016c M) (st fx' R' 0xb0664 M')
        /\ (forall x, In x KS_awvJ3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 722532
        /\ getr R' (reg 11) = Z_to_bv 64 579196
        /\ getr R' (reg 13) = Z_to_bv 64 143344).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G13 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI6 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PawvJ3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvJ3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvJ3.kn0).
  { unfold know_ok, PawvJ3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvJ3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvJ3.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PawvJ3.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvJ3.ps0) with 0xb0664 in Hms. change (SR.ps_regs PawvJ3.ps0) with (map (fun i => (i, nth i PawvJ3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvJ3.ps0) with PawvJ3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvJ3.regs0 PawvJ3.regs_out0 80 KS_awvJ3 KS_awvJ3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvJ3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvJ3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvJ3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvJ3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PawvJ3.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PawvJ3.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvJ4 := LibSegBa_awvJ4_b.
Definition KS_awvJ4 : list nat := Eval vm_compute in (BG.kept_list 80 PawvJ4.regs0 PawvJ4.regs_out0).
Lemma KS_awvJ4_ok : BG.kept_ok 80 PawvJ4.regs0 PawvJ4.regs_out0 KS_awvJ4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvJ4_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 18 -> getr R (reg 13) = Z_to_bv 64 3 -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 4 -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb016c M) (st fx' R' 0xb0890 M')
        /\ (forall x, In x KS_awvJ4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 723088
        /\ getr R' (reg 11) = Z_to_bv 64 579752
        /\ getr R' (reg 13) = Z_to_bv 64 143348).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G13 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI6 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PawvJ4.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvJ4.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvJ4.kn0).
  { unfold know_ok, PawvJ4.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvJ4.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvJ4.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PawvJ4.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvJ4.ps0) with 0xb0890 in Hms. change (SR.ps_regs PawvJ4.ps0) with (map (fun i => (i, nth i PawvJ4.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvJ4.ps0) with PawvJ4.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvJ4.regs0 PawvJ4.regs_out0 80 KS_awvJ4 KS_awvJ4_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvJ4.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvJ4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvJ4.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvJ4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PawvJ4.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PawvJ4.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvJ5 := LibSegBa_awvJ5_b.
Definition KS_awvJ5 : list nat := Eval vm_compute in (BG.kept_list 80 PawvJ5.regs0 PawvJ5.regs_out0).
Lemma KS_awvJ5_ok : BG.kept_ok 80 PawvJ5.regs0 PawvJ5.regs_out0 KS_awvJ5 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvJ5_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 18 -> getr R (reg 13) = Z_to_bv 64 4 -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 5 -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb016c M) (st fx' R' 0xb08a4 M')
        /\ (forall x, In x KS_awvJ5 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 723108
        /\ getr R' (reg 11) = Z_to_bv 64 579772
        /\ getr R' (reg 13) = Z_to_bv 64 143352).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G13 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI6 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PawvJ5.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvJ5.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvJ5.kn0).
  { unfold know_ok, PawvJ5.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvJ5.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvJ5.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PawvJ5.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvJ5.ps0) with 0xb08a4 in Hms. change (SR.ps_regs PawvJ5.ps0) with (map (fun i => (i, nth i PawvJ5.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvJ5.ps0) with PawvJ5.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvJ5.regs0 PawvJ5.regs_out0 80 KS_awvJ5 KS_awvJ5_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvJ5.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvJ5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvJ5.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvJ5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PawvJ5.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PawvJ5.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvJ6 := LibSegBa_awvJ6_b.
Definition KS_awvJ6 : list nat := Eval vm_compute in (BG.kept_list 80 PawvJ6.regs0 PawvJ6.regs_out0).
Lemma KS_awvJ6_ok : BG.kept_ok 80 PawvJ6.regs0 PawvJ6.regs_out0 KS_awvJ6 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvJ6_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 18 -> getr R (reg 13) = Z_to_bv 64 5 -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 6 -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb016c M) (st fx' R' 0xb0b8c M')
        /\ (forall x, In x KS_awvJ6 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 723852
        /\ getr R' (reg 11) = Z_to_bv 64 580516
        /\ getr R' (reg 13) = Z_to_bv 64 143356).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G13 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI6 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PawvJ6.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvJ6.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvJ6.kn0).
  { unfold know_ok, PawvJ6.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvJ6.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvJ6.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PawvJ6.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvJ6.ps0) with 0xb0b8c in Hms. change (SR.ps_regs PawvJ6.ps0) with (map (fun i => (i, nth i PawvJ6.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvJ6.ps0) with PawvJ6.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvJ6.regs0 PawvJ6.regs_out0 80 KS_awvJ6 KS_awvJ6_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvJ6.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvJ6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvJ6.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvJ6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PawvJ6.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PawvJ6.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvJ7 := LibSegBa_awvJ7_b.
Definition KS_awvJ7 : list nat := Eval vm_compute in (BG.kept_list 80 PawvJ7.regs0 PawvJ7.regs_out0).
Lemma KS_awvJ7_ok : BG.kept_ok 80 PawvJ7.regs0 PawvJ7.regs_out0 KS_awvJ7 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvJ7_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 18 -> getr R (reg 13) = Z_to_bv 64 6 -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 7 -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb016c M) (st fx' R' 0xb0ac4 M')
        /\ (forall x, In x KS_awvJ7 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 723652
        /\ getr R' (reg 11) = Z_to_bv 64 580316
        /\ getr R' (reg 13) = Z_to_bv 64 143360).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G13 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI6 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PawvJ7.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvJ7.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvJ7.kn0).
  { unfold know_ok, PawvJ7.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvJ7.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvJ7.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PawvJ7.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvJ7.ps0) with 0xb0ac4 in Hms. change (SR.ps_regs PawvJ7.ps0) with (map (fun i => (i, nth i PawvJ7.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvJ7.ps0) with PawvJ7.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvJ7.regs0 PawvJ7.regs_out0 80 KS_awvJ7 KS_awvJ7_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvJ7.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvJ7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvJ7.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvJ7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PawvJ7.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PawvJ7.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvJ8 := LibSegBa_awvJ8_b.
Definition KS_awvJ8 : list nat := Eval vm_compute in (BG.kept_list 80 PawvJ8.regs0 PawvJ8.regs_out0).
Lemma KS_awvJ8_ok : BG.kept_ok 80 PawvJ8.regs0 PawvJ8.regs_out0 KS_awvJ8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvJ8_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 18 -> getr R (reg 13) = Z_to_bv 64 7 -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 8 -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb016c M) (st fx' R' 0xb0c14 M')
        /\ (forall x, In x KS_awvJ8 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 723988
        /\ getr R' (reg 11) = Z_to_bv 64 580652
        /\ getr R' (reg 13) = Z_to_bv 64 143364).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G13 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI6 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PawvJ8.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvJ8.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvJ8.kn0).
  { unfold know_ok, PawvJ8.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvJ8.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvJ8.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PawvJ8.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvJ8.ps0) with 0xb0c14 in Hms. change (SR.ps_regs PawvJ8.ps0) with (map (fun i => (i, nth i PawvJ8.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvJ8.ps0) with PawvJ8.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvJ8.regs0 PawvJ8.regs_out0 80 KS_awvJ8 KS_awvJ8_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvJ8.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvJ8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvJ8.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvJ8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PawvJ8.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PawvJ8.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvJ9 := LibSegBa_awvJ9_b.
Definition KS_awvJ9 : list nat := Eval vm_compute in (BG.kept_list 80 PawvJ9.regs0 PawvJ9.regs_out0).
Lemma KS_awvJ9_ok : BG.kept_ok 80 PawvJ9.regs0 PawvJ9.regs_out0 KS_awvJ9 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvJ9_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 18 -> getr R (reg 13) = Z_to_bv 64 8 -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 9 -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb016c M) (st fx' R' 0xb0678 M')
        /\ (forall x, In x KS_awvJ9 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 722552
        /\ getr R' (reg 11) = Z_to_bv 64 579216
        /\ getr R' (reg 13) = Z_to_bv 64 143368).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G13 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI6 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PawvJ9.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvJ9.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvJ9.kn0).
  { unfold know_ok, PawvJ9.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvJ9.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvJ9.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PawvJ9.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvJ9.ps0) with 0xb0678 in Hms. change (SR.ps_regs PawvJ9.ps0) with (map (fun i => (i, nth i PawvJ9.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvJ9.ps0) with PawvJ9.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvJ9.regs0 PawvJ9.regs_out0 80 KS_awvJ9 KS_awvJ9_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvJ9.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvJ9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvJ9.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvJ9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PawvJ9.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PawvJ9.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvJ10 := LibSegBa_awvJ10_b.
Definition KS_awvJ10 : list nat := Eval vm_compute in (BG.kept_list 80 PawvJ10.regs0 PawvJ10.regs_out0).
Lemma KS_awvJ10_ok : BG.kept_ok 80 PawvJ10.regs0 PawvJ10.regs_out0 KS_awvJ10 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvJ10_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 18 -> getr R (reg 13) = Z_to_bv 64 9 -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 10 -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb016c M) (st fx' R' 0xb0d2c M')
        /\ (forall x, In x KS_awvJ10 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 724268
        /\ getr R' (reg 11) = Z_to_bv 64 580932
        /\ getr R' (reg 13) = Z_to_bv 64 143372).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G13 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI6 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PawvJ10.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvJ10.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvJ10.kn0).
  { unfold know_ok, PawvJ10.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvJ10.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvJ10.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PawvJ10.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvJ10.ps0) with 0xb0d2c in Hms. change (SR.ps_regs PawvJ10.ps0) with (map (fun i => (i, nth i PawvJ10.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvJ10.ps0) with PawvJ10.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvJ10.regs0 PawvJ10.regs_out0 80 KS_awvJ10 KS_awvJ10_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvJ10.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvJ10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvJ10.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvJ10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PawvJ10.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PawvJ10.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvJ11 := LibSegBa_awvJ11_b.
Definition KS_awvJ11 : list nat := Eval vm_compute in (BG.kept_list 80 PawvJ11.regs0 PawvJ11.regs_out0).
Lemma KS_awvJ11_ok : BG.kept_ok 80 PawvJ11.regs0 PawvJ11.regs_out0 KS_awvJ11 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvJ11_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 18 -> getr R (reg 13) = Z_to_bv 64 10 -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 11 -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb016c M) (st fx' R' 0xb0610 M')
        /\ (forall x, In x KS_awvJ11 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 722448
        /\ getr R' (reg 11) = Z_to_bv 64 579112
        /\ getr R' (reg 13) = Z_to_bv 64 143376).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G13 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI6 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PawvJ11.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvJ11.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvJ11.kn0).
  { unfold know_ok, PawvJ11.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvJ11.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvJ11.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PawvJ11.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvJ11.ps0) with 0xb0610 in Hms. change (SR.ps_regs PawvJ11.ps0) with (map (fun i => (i, nth i PawvJ11.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvJ11.ps0) with PawvJ11.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvJ11.regs0 PawvJ11.regs_out0 80 KS_awvJ11 KS_awvJ11_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvJ11.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvJ11.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvJ11.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvJ11.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PawvJ11.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PawvJ11.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvJ12 := LibSegBa_awvJ12_b.
Definition KS_awvJ12 : list nat := Eval vm_compute in (BG.kept_list 80 PawvJ12.regs0 PawvJ12.regs_out0).
Lemma KS_awvJ12_ok : BG.kept_ok 80 PawvJ12.regs0 PawvJ12.regs_out0 KS_awvJ12 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvJ12_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 18 -> getr R (reg 13) = Z_to_bv 64 11 -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 12 -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb016c M) (st fx' R' 0xb03bc M')
        /\ (forall x, In x KS_awvJ12 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 721852
        /\ getr R' (reg 11) = Z_to_bv 64 578516
        /\ getr R' (reg 13) = Z_to_bv 64 143380).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G13 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI6 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PawvJ12.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvJ12.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvJ12.kn0).
  { unfold know_ok, PawvJ12.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvJ12.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvJ12.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PawvJ12.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvJ12.ps0) with 0xb03bc in Hms. change (SR.ps_regs PawvJ12.ps0) with (map (fun i => (i, nth i PawvJ12.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvJ12.ps0) with PawvJ12.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvJ12.regs0 PawvJ12.regs_out0 80 KS_awvJ12 KS_awvJ12_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvJ12.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvJ12.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvJ12.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvJ12.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PawvJ12.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PawvJ12.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvJ13 := LibSegBa_awvJ13_b.
Definition KS_awvJ13 : list nat := Eval vm_compute in (BG.kept_list 80 PawvJ13.regs0 PawvJ13.regs_out0).
Lemma KS_awvJ13_ok : BG.kept_ok 80 PawvJ13.regs0 PawvJ13.regs_out0 KS_awvJ13 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvJ13_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 18 -> getr R (reg 13) = Z_to_bv 64 12 -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 13 -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb016c M) (st fx' R' 0xb07a0 M')
        /\ (forall x, In x KS_awvJ13 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 722848
        /\ getr R' (reg 11) = Z_to_bv 64 579512
        /\ getr R' (reg 13) = Z_to_bv 64 143384).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G13 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI6 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PawvJ13.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvJ13.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvJ13.kn0).
  { unfold know_ok, PawvJ13.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvJ13.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvJ13.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PawvJ13.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvJ13.ps0) with 0xb07a0 in Hms. change (SR.ps_regs PawvJ13.ps0) with (map (fun i => (i, nth i PawvJ13.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvJ13.ps0) with PawvJ13.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvJ13.regs0 PawvJ13.regs_out0 80 KS_awvJ13 KS_awvJ13_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvJ13.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvJ13.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvJ13.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvJ13.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PawvJ13.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PawvJ13.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvJ14 := LibSegBa_awvJ14_b.
Definition KS_awvJ14 : list nat := Eval vm_compute in (BG.kept_list 80 PawvJ14.regs0 PawvJ14.regs_out0).
Lemma KS_awvJ14_ok : BG.kept_ok 80 PawvJ14.regs0 PawvJ14.regs_out0 KS_awvJ14 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvJ14_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 18 -> getr R (reg 13) = Z_to_bv 64 13 -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 14 -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb016c M) (st fx' R' 0xb02c4 M')
        /\ (forall x, In x KS_awvJ14 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 721604
        /\ getr R' (reg 11) = Z_to_bv 64 578268
        /\ getr R' (reg 13) = Z_to_bv 64 143388).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G13 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI6 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PawvJ14.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvJ14.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvJ14.kn0).
  { unfold know_ok, PawvJ14.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvJ14.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvJ14.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PawvJ14.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvJ14.ps0) with 0xb02c4 in Hms. change (SR.ps_regs PawvJ14.ps0) with (map (fun i => (i, nth i PawvJ14.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvJ14.ps0) with PawvJ14.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvJ14.regs0 PawvJ14.regs_out0 80 KS_awvJ14 KS_awvJ14_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvJ14.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvJ14.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvJ14.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvJ14.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PawvJ14.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PawvJ14.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvJ15 := LibSegBa_awvJ15_b.
Definition KS_awvJ15 : list nat := Eval vm_compute in (BG.kept_list 80 PawvJ15.regs0 PawvJ15.regs_out0).
Lemma KS_awvJ15_ok : BG.kept_ok 80 PawvJ15.regs0 PawvJ15.regs_out0 KS_awvJ15 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvJ15_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 18 -> getr R (reg 13) = Z_to_bv 64 14 -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 15 -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb016c M) (st fx' R' 0xb03bc M')
        /\ (forall x, In x KS_awvJ15 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 721852
        /\ getr R' (reg 11) = Z_to_bv 64 578516
        /\ getr R' (reg 13) = Z_to_bv 64 143392).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G13 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI6 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PawvJ15.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvJ15.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvJ15.kn0).
  { unfold know_ok, PawvJ15.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvJ15.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvJ15.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PawvJ15.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvJ15.ps0) with 0xb03bc in Hms. change (SR.ps_regs PawvJ15.ps0) with (map (fun i => (i, nth i PawvJ15.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvJ15.ps0) with PawvJ15.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvJ15.regs0 PawvJ15.regs_out0 80 KS_awvJ15 KS_awvJ15_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvJ15.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvJ15.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvJ15.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvJ15.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PawvJ15.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PawvJ15.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvJ16 := LibSegBa_awvJ16_b.
Definition KS_awvJ16 : list nat := Eval vm_compute in (BG.kept_list 80 PawvJ16.regs0 PawvJ16.regs_out0).
Lemma KS_awvJ16_ok : BG.kept_ok 80 PawvJ16.regs0 PawvJ16.regs_out0 KS_awvJ16 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvJ16_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 18 -> getr R (reg 13) = Z_to_bv 64 15 -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 16 -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb016c M) (st fx' R' 0xb0da8 M')
        /\ (forall x, In x KS_awvJ16 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 724392
        /\ getr R' (reg 11) = Z_to_bv 64 581056
        /\ getr R' (reg 13) = Z_to_bv 64 143396).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G13 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI6 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PawvJ16.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvJ16.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvJ16.kn0).
  { unfold know_ok, PawvJ16.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvJ16.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvJ16.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PawvJ16.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvJ16.ps0) with 0xb0da8 in Hms. change (SR.ps_regs PawvJ16.ps0) with (map (fun i => (i, nth i PawvJ16.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvJ16.ps0) with PawvJ16.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvJ16.regs0 PawvJ16.regs_out0 80 KS_awvJ16 KS_awvJ16_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvJ16.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvJ16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvJ16.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvJ16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PawvJ16.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PawvJ16.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvJ17 := LibSegBa_awvJ17_b.
Definition KS_awvJ17 : list nat := Eval vm_compute in (BG.kept_list 80 PawvJ17.regs0 PawvJ17.regs_out0).
Lemma KS_awvJ17_ok : BG.kept_ok 80 PawvJ17.regs0 PawvJ17.regs_out0 KS_awvJ17 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvJ17_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 18 -> getr R (reg 13) = Z_to_bv 64 16 -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 17 -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb016c M) (st fx' R' 0xb0eac M')
        /\ (forall x, In x KS_awvJ17 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 724652
        /\ getr R' (reg 11) = Z_to_bv 64 581316
        /\ getr R' (reg 13) = Z_to_bv 64 143400).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G13 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI6 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PawvJ17.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvJ17.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvJ17.kn0).
  { unfold know_ok, PawvJ17.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvJ17.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvJ17.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PawvJ17.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvJ17.ps0) with 0xb0eac in Hms. change (SR.ps_regs PawvJ17.ps0) with (map (fun i => (i, nth i PawvJ17.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvJ17.ps0) with PawvJ17.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvJ17.regs0 PawvJ17.regs_out0 80 KS_awvJ17 KS_awvJ17_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvJ17.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvJ17.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvJ17.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvJ17.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PawvJ17.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PawvJ17.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvJ18 := LibSegBa_awvJ18_b.
Definition KS_awvJ18 : list nat := Eval vm_compute in (BG.kept_list 80 PawvJ18.regs0 PawvJ18.regs_out0).
Lemma KS_awvJ18_ok : BG.kept_ok 80 PawvJ18.regs0 PawvJ18.regs_out0 KS_awvJ18 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvJ18_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 18 -> getr R (reg 13) = Z_to_bv 64 17 -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 18 -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb016c M) (st fx' R' 0xb03e8 M')
        /\ (forall x, In x KS_awvJ18 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 721896
        /\ getr R' (reg 11) = Z_to_bv 64 578560
        /\ getr R' (reg 13) = Z_to_bv 64 143404).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G13 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI6 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PawvJ18.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvJ18.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvJ18.kn0).
  { unfold know_ok, PawvJ18.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvJ18.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvJ18.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PawvJ18.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvJ18.ps0) with 0xb03e8 in Hms. change (SR.ps_regs PawvJ18.ps0) with (map (fun i => (i, nth i PawvJ18.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvJ18.ps0) with PawvJ18.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvJ18.regs0 PawvJ18.regs_out0 80 KS_awvJ18 KS_awvJ18_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvJ18.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvJ18.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvJ18.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvJ18.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PawvJ18.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PawvJ18.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvJ19 := LibSegBa_awvJ19_b.
Definition KS_awvJ19 : list nat := Eval vm_compute in (BG.kept_list 80 PawvJ19.regs0 PawvJ19.regs_out0).
Lemma KS_awvJ19_ok : BG.kept_ok 80 PawvJ19.regs0 PawvJ19.regs_out0 KS_awvJ19 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvJ19_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 18 -> getr R (reg 13) = Z_to_bv 64 18 -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 19 -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb016c M) (st fx' R' 0xb0514 M')
        /\ (forall x, In x KS_awvJ19 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 722196
        /\ getr R' (reg 11) = Z_to_bv 64 578860
        /\ getr R' (reg 13) = Z_to_bv 64 143408).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G13 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI6 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PawvJ19.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvJ19.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvJ19.kn0).
  { unfold know_ok, PawvJ19.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvJ19.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvJ19.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PawvJ19.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvJ19.ps0) with 0xb0514 in Hms. change (SR.ps_regs PawvJ19.ps0) with (map (fun i => (i, nth i PawvJ19.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvJ19.ps0) with PawvJ19.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvJ19.regs0 PawvJ19.regs_out0 80 KS_awvJ19 KS_awvJ19_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvJ19.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvJ19.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvJ19.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvJ19.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PawvJ19.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PawvJ19.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvJ127 := LibSegBa_awvJ127_b.
Definition KS_awvJ127 : list nat := Eval vm_compute in (BG.kept_list 80 PawvJ127.regs0 PawvJ127.regs_out0).
Lemma KS_awvJ127_ok : BG.kept_ok 80 PawvJ127.regs0 PawvJ127.regs_out0 KS_awvJ127 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvJ127_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 18 -> getr R (reg 13) = Z_to_bv 64 126 -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 127 -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb016c M) (st fx' R' 0xb02c4 M')
        /\ (forall x, In x KS_awvJ127 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 127).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G13 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI6 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PawvJ127.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvJ127.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvJ127.kn0).
  { unfold know_ok, PawvJ127.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvJ127.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvJ127.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PawvJ127.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvJ127.ps0) with 0xb02c4 in Hms. change (SR.ps_regs PawvJ127.ps0) with (map (fun i => (i, nth i PawvJ127.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvJ127.ps0) with PawvJ127.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvJ127.regs0 PawvJ127.regs_out0 80 KS_awvJ127 KS_awvJ127_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg PawvJ127.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvJ127.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvJ255 := LibSegBa_awvJ255_b.
Definition KS_awvJ255 : list nat := Eval vm_compute in (BG.kept_list 80 PawvJ255.regs0 PawvJ255.regs_out0).
Lemma KS_awvJ255_ok : BG.kept_ok 80 PawvJ255.regs0 PawvJ255.regs_out0 KS_awvJ255 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvJ255_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 18 -> getr R (reg 13) = Z_to_bv 64 254 -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 255 -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb016c M) (st fx' R' 0xb02c4 M')
        /\ (forall x, In x KS_awvJ255 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 255).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G13 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI6 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PawvJ255.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvJ255.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvJ255.kn0).
  { unfold know_ok, PawvJ255.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvJ255.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvJ255.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PawvJ255.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvJ255.ps0) with 0xb02c4 in Hms. change (SR.ps_regs PawvJ255.ps0) with (map (fun i => (i, nth i PawvJ255.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvJ255.ps0) with PawvJ255.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvJ255.regs0 PawvJ255.regs_out0 80 KS_awvJ255 KS_awvJ255_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg PawvJ255.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvJ255.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvJ0 := LibSegBa_awvJ0_b.
Definition KS_awvJ0 : list nat := Eval vm_compute in (BG.kept_list 80 PawvJ0.regs0 PawvJ0.regs_out0).
Lemma KS_awvJ0_ok : BG.kept_ok 80 PawvJ0.regs0 PawvJ0.regs_out0 KS_awvJ0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvJ0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 18 -> getr R (reg 13) = Z_to_bv 64 18446744073709551615 -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 0 -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb016c M) (st fx' R' 0xb03bc M')
        /\ (forall x, In x KS_awvJ0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 255).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G13 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI6 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PawvJ0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvJ0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvJ0.kn0).
  { unfold know_ok, PawvJ0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvJ0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvJ0.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PawvJ0.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvJ0.ps0) with 0xb03bc in Hms. change (SR.ps_regs PawvJ0.ps0) with (map (fun i => (i, nth i PawvJ0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvJ0.ps0) with PawvJ0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvJ0.regs0 PawvJ0.regs_out0 80 KS_awvJ0 KS_awvJ0_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg PawvJ0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvJ0.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvJr1 := LibSegBa_awvJr1_b.
Definition KS_awvJr1 : list nat := Eval vm_compute in (BG.kept_list 80 PawvJr1.regs0 PawvJr1.regs_out0).
Lemma KS_awvJr1_ok : BG.kept_ok 80 PawvJr1.regs0 PawvJr1.regs_out0 KS_awvJr1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvJr1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 18 -> getr R (reg 13) = Z_to_bv 64 ((V 35%nat) - 1) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 (V 35%nat) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 20 <= (V 35%nat) <= 126 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb016c M) (st fx' R' 0xb03bc M')
        /\ (forall x, In x KS_awvJr1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 255).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G10 G13 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV50l; move HV50l before pvzI6; pose proof (proj2 pvzI6) as HV50r; move HV50r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PawvJr1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvJr1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvJr1.kn0).
  { unfold know_ok, PawvJr1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvJr1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvJr1.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PawvJr1.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvJr1.ps0) with 0xb03bc in Hms. change (SR.ps_regs PawvJr1.ps0) with (map (fun i => (i, nth i PawvJr1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvJr1.ps0) with PawvJr1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvJr1.regs0 PawvJr1.regs_out0 80 KS_awvJr1 KS_awvJr1_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg PawvJr1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvJr1.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvJr2 := LibSegBa_awvJr2_b.
Definition KS_awvJr2 : list nat := Eval vm_compute in (BG.kept_list 80 PawvJr2.regs0 PawvJr2.regs_out0).
Lemma KS_awvJr2_ok : BG.kept_ok 80 PawvJr2.regs0 PawvJr2.regs_out0 KS_awvJr2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvJr2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 18 -> getr R (reg 13) = Z_to_bv 64 ((V 35%nat) - 1) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 (V 35%nat) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 128 <= (V 35%nat) <= 254 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb016c M) (st fx' R' 0xb03bc M')
        /\ (forall x, In x KS_awvJr2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 255).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G10 G13 G18 G19 G20 G21 G22 G23 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV50l; move HV50l before pvzI6; pose proof (proj2 pvzI6) as HV50r; move HV50r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PawvJr2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvJr2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvJr2.kn0).
  { unfold know_ok, PawvJr2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvJr2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvJr2.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PawvJr2.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvJr2.ps0) with 0xb03bc in Hms. change (SR.ps_regs PawvJr2.ps0) with (map (fun i => (i, nth i PawvJr2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvJr2.ps0) with PawvJr2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvJr2.regs0 PawvJr2.regs_out0 80 KS_awvJr2 KS_awvJr2_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg PawvJr2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvJr2.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

End PNARVTP.
