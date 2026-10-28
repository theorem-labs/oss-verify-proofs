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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require LibSegBa_aenA_b LibSegBa_aenB0_b LibSegBa_aenCS_b LibSegBa_aenCL_b LibSegBa_aenR_b LibSegBa_aenT_b LibSegBa_aenVS_b LibSegBa_aenVL_b LibSegBa_aenC_b LibSegBa_aenE_b LibSegBa_aenKS_b LibSegBa_aenKL_b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNAENP.
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
Module PaenA := LibSegBa_aenA_b.
Definition KS_aenA : list nat := Eval vm_compute in (BG.kept_list 80 PaenA.regs0 PaenA.regs_out0).
Lemma KS_aenA_ok : BG.kept_ok 80 PaenA.regs0 PaenA.regs_out0 KS_aenA = true. Proof. vm_compute. reflexivity. Qed.
Lemma aenA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) -> getr R (reg 13) = Z_to_bv 64 (V 36%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xaf548 M) (st fx' R' 0x5dc2c M')
        /\ (forall x, In x KS_aenA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 718276
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 10) = Z_to_bv 64 64
        /\ getr R' (reg 11) = Z_to_bv 64 1309752
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 19) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 2147450880
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G10 G11 G12 G13 K0 K1 K2 pvzI6 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PaenA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaenA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaenA.kn0).
  { unfold know_ok, PaenA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaenA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaenA.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 128) <= bv_unsigned a < (vz_2 - 128) + 128) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PaenA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaenA.ps0) with 0x5dc2c in Hms. change (SR.ps_regs PaenA.ps0) with (map (fun i => (i, nth i PaenA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaenA.ps0) with PaenA.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaenA.regs0 PaenA.regs_out0 80 KS_aenA KS_aenA_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaenA.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaenA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenA.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaenA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenA.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaenA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenA.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PaenA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenA.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaenA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenA.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaenA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenA.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PaenA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenA.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaenA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenA.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PaenA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenA.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PaenA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenA.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PaenA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenA.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PaenA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
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
Module PaenB0 := LibSegBa_aenB0_b.
Definition KS_aenB0 : list nat := Eval vm_compute in (BG.kept_list 80 PaenB0.regs0 PaenB0.regs_out0).
Lemma KS_aenB0_ok : BG.kept_ok 80 PaenB0.regs0 PaenB0.regs_out0 KS_aenB0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma aenB0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 50%nat) -> getr R (reg 19) = Z_to_bv 64 (V 33%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 (V 35%nat) -> getr R (reg 25) = Z_to_bv 64 2147450880 ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6905856 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 -> 6905856 <= (V 50%nat) <= 140737488355264 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 64 ->
  L5.writable RSEGS M (V 50%nat) 64 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 50%nat) + 56) (V 51%nat) ->
  4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 64 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) ->
  (((V 2%nat) - 128) + 128 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 128)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 24) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 24) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xaf5c4 M) (st fx' R' 0xaf658 M')
        /\ (forall x, In x KS_aenB0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 1102416563
        /\ getr R' (reg 11) = Z_to_bv 64 120859
        /\ getr R' (reg 12) = Z_to_bv 64 718152
        /\ getr R' (reg 13) = Z_to_bv 64 18446744073709551603
        /\ getr R' (reg 14) = Z_to_bv 64 18446744073709551608
        /\ getr R' (reg 15) = Z_to_bv 64 18446744073709551601
        /\ getr R' (reg 18) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 33%nat) + 344)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880)
        /\ getr R' (reg 27) = Z_to_bv 64 ((((V 33%nat) + 344) / 8) + 2147450880)
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450883) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450882) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450881) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450880) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450887) 243
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450886) 243
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450885) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450884) 248
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 16) 718152
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 8) 120859
        /\ L5.u64_at RSEGS M' (V 50%nat) 1102416563
        /\ L5.defined M' ((V 50%nat) + 24) 40).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G19 G20 G21 G23 G25 pvzI8 K1 K2 pvzI9 K4 pvzI10 K6 K7 K8 K9 K10 K11 pvzI11 K13 K14 K15 K16 K17.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV50l; move HV50l before pvzI6; pose proof (proj2 pvzI6) as HV50r; move HV50r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV51l; move HV51l before pvzI7; pose proof (proj2 pvzI7) as HV51r; move HV51r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K5l; move K5l before pvzI10; pose proof (proj2 pvzI10) as K5r; move K5r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K12l; move K12l before pvzI11; pose proof (proj2 pvzI11) as K12r; move K12r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PaenB0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaenB0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaenB0.kn0).
  { unfold know_ok, PaenB0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K17) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K17) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K17) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K17; lia | clear - HV2l HV2r K0l K0r K16 K17; lia | clear - HV2l HV2r K0l K0r K16 K17; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | clear; lia | exact K6]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K5l K5r K9 K15 K16; lia | clear - HV50l HV50r K5l K5r K9 K15 K16; lia | clear - HV50l HV50r K5l K5r K9 K15 K16; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K5l K5r K9 K15 K16; lia | clear - HV50l HV50r K5l K5r K9 K15 K16; lia | clear - HV50l HV50r K5l K5r K9 K15 K16; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K5l K5r K9 K15 K16; lia | clear - HV50l HV50r K5l K5r K9 K15 K16; lia | clear - HV50l HV50r K5l K5r K9 K15 K16; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk ZA ltac:(clear - HV51l HV51r K12l K12r K14 K15 K17) | clear - HV50l HV50r K5l K5r K9 K15 K16; lia | clear - HV50l HV50r K5l K5r K9 K15 K16; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K12l K12r K14 K15 K17) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K12l K12r K14 K15 K17) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K12l K12r K14 K15 K17; lia | clear - HV51l HV51r K12l K12r K14 K15 K17; lia | clear - HV51l HV51r K12l K12r K14 K15 K17; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K12l K12r K14 K15 K17) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K12l K12r K14 K15 K17) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K12l K12r K14 K15 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaenB0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaenB0.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 24) -> ~ ((((vz_50 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 0) + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PaenB0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K5l K5r K9 K15 K16 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K5l K5r K9 K15 K16 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaenB0.ps0) with 0xaf658 in Hms. change (SR.ps_regs PaenB0.ps0) with (map (fun i => (i, nth i PaenB0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaenB0.ps0) with PaenB0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaenB0.regs0 PaenB0.regs_out0 80 KS_aenB0 KS_aenB0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaenB0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaenB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenB0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaenB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenB0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PaenB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenB0.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PaenB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenB0.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PaenB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenB0.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PaenB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenB0.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaenB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenB0.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PaenB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenB0.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PaenB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenB0.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PaenB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenB0.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PaenB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PaenCS := LibSegBa_aenCS_b.
Definition KS_aenCS : list nat := Eval vm_compute in (BG.kept_list 80 PaenCS.regs0 PaenCS.regs_out0).
Lemma KS_aenCS_ok : BG.kept_ok 80 PaenCS.regs0 PaenCS.regs_out0 KS_aenCS = true. Proof. vm_compute. reflexivity. Qed.
Lemma aenCS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 18) = Z_to_bv 64 (V 50%nat) -> getr R (reg 19) = Z_to_bv 64 (V 33%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 34%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 33%nat) + 344) -> getr R (reg 23) = Z_to_bv 64 (V 35%nat) -> getr R (reg 24) = Z_to_bv 64 (V 50%nat) -> getr R (reg 25) = Z_to_bv 64 2147450880 -> getr R (reg 26) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 ((((V 33%nat) + 344) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 344) / 8) + 2147450880) 3 ->
  L5KA.zeros_at M ((((V 33%nat) + 345) / 8) + 2147450880) 1 -> (((V 2%nat) - 128) + 128 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 128)) -> 6905856 <= (V 50%nat) <= 140737488355264 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 64 -> L5.writable RSEGS M (V 50%nat) 64 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 8 ->
  L5.u64_at RSEGS M ((V 50%nat) + 56) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 64 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 128) + 128 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 128)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 64 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u8_at RSEGS M ((V 33%nat) + 344) (V 42%nat) -> 0 <= (V 42%nat) <= 255 ->
  Z.testbit (V 42%nat) 0 = false -> L5.writable RSEGS M ((V 33%nat) + 344) 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 112) <= bv_unsigned a < ((V 2%nat) - 112) + 8) -> ~ (((V 33%nat) + 344) <= bv_unsigned a < ((V 33%nat) + 344) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 112) <= i < ((V 2%nat) - 112) + 8) -> ~ (((V 33%nat) + 344) <= i < ((V 33%nat) + 344) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xaf658 M) (st fx' R' 0xb2cd0 M')
        /\ (forall x, In x KS_aenCS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 718576
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 344)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 36%nat)
        /\ L5.u8_at RSEGS M' ((V 33%nat) + 344) 0
        /\ L5.u8_at RSEGS M' ((V 33%nat) + 345) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 50%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI9 K4 K5 pvzI10 K7 K8 K9 K10 K11 K12 K13 pvzI11 K15 K16 K17 K18 K19 K20 pvzI12 K22 K23 K24 K25 K26 K27 K28 K29 K30 pvzI13 K32 K33.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV42l; move HV42l before pvzI6; pose proof (proj2 pvzI6) as HV42r; move HV42r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV50l; move HV50l before pvzI7; pose proof (proj2 pvzI7) as HV50r; move HV50r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV51l; move HV51l before pvzI8; pose proof (proj2 pvzI8) as HV51r; move HV51r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K14l; move K14l before pvzI11; pose proof (proj2 pvzI11) as K14r; move K14r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K21l; move K21l before pvzI12; pose proof (proj2 pvzI12) as K21r; move K21r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K31l; move K31l before pvzI13; pose proof (proj2 pvzI13) as K31r; move K31r before pvzI13; clear pvzI13.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 42%nat => Z_to_bv 64 vz_42 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 42%nat => vz_42 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PaenCS.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaenCS.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaenCS.kn0).
  { unfold know_ok, PaenCS.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K21l K21r K23 K24 K26 K28; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear - HV42l HV42r K31l K31r K32) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | byte_tac ltac:(clear - HV42l HV42r K31l K31r K32) | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K31l K31r K32) | exact (conj K31l K31r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV42l HV42r K31l K31r K32) | clear; lia | rewrite (L5K.land1_bit0_false vz_42 ltac:(clear - HV42l HV42r K31l K31r K32; lia) K32); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K33]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaenCS.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaenCS.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 112) <= bv_unsigned a < (vz_2 - 112) + 8) -> ~ ((vz_33 + 344) <= bv_unsigned a < (vz_33 + 344) + 2) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PaenCS.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaenCS.ps0) with 0xb2cd0 in Hms. change (SR.ps_regs PaenCS.ps0) with (map (fun i => (i, nth i PaenCS.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaenCS.ps0) with PaenCS.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaenCS.regs0 PaenCS.regs_out0 80 KS_aenCS KS_aenCS_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaenCS.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaenCS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenCS.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaenCS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenCS.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaenCS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenCS.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PaenCS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PaenCL := LibSegBa_aenCL_b.
Definition KS_aenCL : list nat := Eval vm_compute in (BG.kept_list 80 PaenCL.regs0 PaenCL.regs_out0).
Lemma KS_aenCL_ok : BG.kept_ok 80 PaenCL.regs0 PaenCL.regs_out0 KS_aenCL = true. Proof. vm_compute. reflexivity. Qed.
Lemma aenCL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 18) = Z_to_bv 64 (V 50%nat) -> getr R (reg 19) = Z_to_bv 64 (V 33%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 34%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 33%nat) + 344) -> getr R (reg 23) = Z_to_bv 64 (V 35%nat) -> getr R (reg 24) = Z_to_bv 64 (V 50%nat) -> getr R (reg 25) = Z_to_bv 64 2147450880 -> getr R (reg 26) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 ((((V 33%nat) + 344) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 344) / 8) + 2147450880) 3 ->
  L5KA.zeros_at M ((((V 33%nat) + 345) / 8) + 2147450880) 1 -> (((V 2%nat) - 128) + 128 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 128)) -> 6905856 <= (V 50%nat) <= 140737488355264 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 64 -> L5.writable RSEGS M (V 50%nat) 64 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 8 ->
  L5.u64_at RSEGS M ((V 50%nat) + 56) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 64 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 128) + 128 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 128)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 64 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u8_at RSEGS M ((V 33%nat) + 344) (V 42%nat) -> 0 <= (V 42%nat) <= 255 ->
  Z.testbit (V 42%nat) 0 = true -> L5.u64_at RSEGS M ((V 33%nat) + 360) (V 43%nat) -> 4096 <= (V 43%nat) <= 140737488355296 -> (2147446784 + 17592186048512 <= (V 43%nat) \/ (V 43%nat) + 1 <= 2147446784) ->
  L5KA.zeros_at M (((V 43%nat) / 8) + 2147450880) 1 -> ((((V 43%nat) / 8) + 2147450880) + 1 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 43%nat) / 8) + 2147450880)) -> L5.writable RSEGS M (V 43%nat) 1 -> (((V 2%nat) - 128) + 128 <= (V 43%nat) \/ (V 43%nat) + 1 <= ((V 2%nat) - 128)) ->
  ((V 43%nat) + 1 <= (V 33%nat) \/ (V 33%nat) + 416 <= (V 43%nat)) -> ((V 43%nat) + 1 <= (V 50%nat) \/ (V 50%nat) + 64 <= (V 43%nat)) -> ((V 43%nat) + 1 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 43%nat)) -> L5.writable RSEGS M ((V 33%nat) + 352) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 112) <= bv_unsigned a < ((V 2%nat) - 112) + 8) -> ~ (((V 43%nat) + 0) <= bv_unsigned a < ((V 43%nat) + 0) + 1) -> ~ (((V 33%nat) + 352) <= bv_unsigned a < ((V 33%nat) + 352) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 112) <= i < ((V 2%nat) - 112) + 8) -> ~ (((V 43%nat) + 0) <= i < ((V 43%nat) + 0) + 1) -> ~ (((V 33%nat) + 352) <= i < ((V 33%nat) + 352) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xaf658 M) (st fx' R' 0xb2cd0 M')
        /\ (forall x, In x KS_aenCL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 718576
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 344)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 352) 0
        /\ L5.u8_at RSEGS M' (V 43%nat) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 50%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI10 K4 K5 pvzI11 K7 K8 K9 K10 K11 K12 K13 pvzI12 K15 K16 K17 K18 K19 K20 pvzI13 K22 K23 K24 K25 K26 K27 K28 K29 K30 pvzI14 K32 K33 pvzI15 K35 K36 K37 K38 K39 K40 K41 K42 K43.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV42l; move HV42l before pvzI6; pose proof (proj2 pvzI6) as HV42r; move HV42r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV43l; move HV43l before pvzI7; pose proof (proj2 pvzI7) as HV43r; move HV43r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV50l; move HV50l before pvzI8; pose proof (proj2 pvzI8) as HV50r; move HV50r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV51l; move HV51l before pvzI9; pose proof (proj2 pvzI9) as HV51r; move HV51r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K6l; move K6l before pvzI11; pose proof (proj2 pvzI11) as K6r; move K6r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K14l; move K14l before pvzI12; pose proof (proj2 pvzI12) as K14r; move K14r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K21l; move K21l before pvzI13; pose proof (proj2 pvzI13) as K21r; move K21r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K31l; move K31l before pvzI14; pose proof (proj2 pvzI14) as K31r; move K31r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K34l; move K34l before pvzI15; pose proof (proj2 pvzI15) as K34r; move K34r before pvzI15; clear pvzI15.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 42%nat => vz_42 | 43%nat => vz_43 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PaenCL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaenCL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaenCL.kn0).
  { unfold know_ok, PaenCL.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K39) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K39) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K39) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K39; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K39; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K39; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K40) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K40) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K40) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K40) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K40; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K40; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K40; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K40) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K40; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K40; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K40; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K40) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K40; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K40; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K40; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K40) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K40; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K40; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K40; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K40) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K41) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K41) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K41) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K41; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K41; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K41; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K41) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K41; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K41; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K41; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K41) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K41) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K41; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K41; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K41; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K41) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K42) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K41; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K41; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K42) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K42) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K42; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K42; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K42; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K42) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K41) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K42) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K41) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K42) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K41) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K42) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K41) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K40) | evalEk ZA ltac:(clear - HV42l HV42r K31l K31r K32) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K40; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K40; lia | byte_tac ltac:(clear - HV42l HV42r K31l K31r K32) | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K31l K31r K32) | exact (conj K31l K31r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV42l HV42r K31l K31r K32) | clear; lia | rewrite (L5K.land1_bit0_true vz_42 ltac:(clear - HV42l HV42r K31l K31r K32; lia) K32); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K40) | evalEk ZA ltac:(clear - HV43l HV43r K34l K34r K35 K37 K39 K40 K41 K42) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K40; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K40; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K34l K34r K35 K37 K39 K40 K41 K42) | exact (conj K34l K34r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV43l HV43r K34l K34r K35 K37 K39 K40 K41 K42) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV43l HV43r K34l K34r K35 K37 K39 K40 K41 K42) | evalEk ZA ltac:(clear) | clear - HV43l HV43r K34l K34r K35 K37 K39 K40 K41 K42; lia | clear - HV43l HV43r K34l K34r K35 K37 K39 K40 K41 K42; lia | clear - HV43l HV43r K34l K34r K35 K37 K39 K40 K41 K42; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV43l HV43r K34l K34r K35 K37 K39 K40 K41 K42) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K41) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV43l HV43r K34l K34r K35 K37 K39 K40 K41 K42) | evalEk ZA ltac:(clear) | clear - HV43l HV43r K34l K34r K35 K37 K39 K40 K41 K42; lia | clear - HV43l HV43r K34l K34r K35 K37 K39 K40 K41 K42; lia | clear - HV43l HV43r K34l K34r K35 K37 K39 K40 K41 K42; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV43l HV43r K34l K34r K35 K37 K39 K40 K41 K42) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV43l HV43r K34l K34r K35 K37 K39 K40 K41 K42) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K40) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV43l HV43r K34l K34r K35 K37 K39 K40 K41 K42) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K41) | evalEk ZA ltac:(clear) | generalize K41; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV43l HV43r K34l K34r K35 K37 K39 K40 K41 K42) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K42) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K40) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K40; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K40; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K40; lia | exactA K43]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaenCL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaenCL.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 112) <= bv_unsigned a < (vz_2 - 112) + 8) -> ~ ((vz_43 + 0) <= bv_unsigned a < (vz_43 + 0) + 1) -> ~ ((vz_33 + 352) <= bv_unsigned a < (vz_33 + 352) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PaenCL.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K39) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K39 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV43l HV43r K34l K34r K35 K37 K39 K40 K41 K42) | evalEk' ZA Hag ltac:(clear) | clear - HV43l HV43r K34l K34r K35 K37 K39 K40 K41 K42 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K40) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K40 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaenCL.ps0) with 0xb2cd0 in Hms. change (SR.ps_regs PaenCL.ps0) with (map (fun i => (i, nth i PaenCL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaenCL.ps0) with PaenCL.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaenCL.regs0 PaenCL.regs_out0 80 KS_aenCL KS_aenCL_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaenCL.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaenCL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenCL.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaenCL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenCL.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaenCL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenCL.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PaenCL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K40) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV43l HV43r K34l K34r K35 K37 K39 K40 K41 K42) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K39) | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K41) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PaenR := LibSegBa_aenR_b.
Definition KS_aenR_0 : list nat := Eval vm_compute in (BG.kept_list 80 PaenR.regs0 PaenR.regs_out0).
Lemma KS_aenR_0_ok : BG.kept_ok 80 PaenR.regs0 PaenR.regs_out0 KS_aenR_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_aenR_1 : list nat := Eval vm_compute in (BG.kept_list 80 PaenR.regs0 PaenR.regs_out1).
Lemma KS_aenR_1_ok : BG.kept_ok 80 PaenR.regs0 PaenR.regs_out1 KS_aenR_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma aenR_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 18) = Z_to_bv 64 (V 50%nat) -> getr R (reg 19) = Z_to_bv 64 (V 33%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 34%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 33%nat) + 344) -> getr R (reg 23) = Z_to_bv 64 (V 35%nat) -> getr R (reg 24) = Z_to_bv 64 (V 50%nat) -> getr R (reg 25) = Z_to_bv 64 2147450880 -> getr R (reg 26) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 ((((V 33%nat) + 344) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 344) / 8) + 2147450880) 3 ->
  L5KA.zeros_at M ((((V 33%nat) + 345) / 8) + 2147450880) 1 -> (((V 2%nat) - 128) + 128 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 128)) -> 6905856 <= (V 50%nat) <= 140737488355264 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 64 -> L5.writable RSEGS M (V 50%nat) 64 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 8 ->
  L5.u64_at RSEGS M ((V 50%nat) + 56) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 64 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 128) + 128 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 128)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 64 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 33%nat) / 8) + 2147450880)) -> 0 <= (V 35%nat) <= 1 -> 6905856 <= (V 36%nat) <= 140737488355312 ->
  aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 2 -> (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + 16 <= ((V 2%nat) - 128)) ->
  ((V 33%nat) + 416 <= (V 36%nat) \/ (V 36%nat) + 16 <= (V 33%nat)) -> ((V 50%nat) + 64 <= (V 36%nat) \/ (V 36%nat) + 16 <= (V 50%nat)) -> ((V 51%nat) + 1 <= (V 36%nat) \/ (V 36%nat) + 16 <= (V 51%nat)) -> L5.u32_at RSEGS M (V 36%nat) (V 44%nat) ->
  0 <= (V 44%nat) <= 64 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xaf6f0 M) (st fx' R' 0xaf854 M')
        /\ (forall x, In x KS_aenR_0 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 10)) = (Z.lor (V 44%nat) (V 35%nat))
        /\ 1 <= (((Z.lor (V 44%nat) (V 35%nat)) - 0) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xaf6f0 M) (st fx' R' 0xaf70c M')
        /\ (forall x, In x KS_aenR_1 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 10)) = (Z.lor (V 44%nat) (V 35%nat))
        /\ (((Z.lor (V 44%nat) (V 35%nat)) - 0) mod 2 ^ 64) < 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI9 K4 K5 pvzI10 K7 K8 K9 K10 K11 K12 K13 pvzI11 K15 K16 K17 K18 K19 K20 pvzI12 K22 K23 K24 K25 K26 K27 K28 K29 pvzI13 pvzI14 K32 K33 K34 K35 K36 K37 K38 K39 pvzI15.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV44l; move HV44l before pvzI6; pose proof (proj2 pvzI6) as HV44r; move HV44r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV50l; move HV50l before pvzI7; pose proof (proj2 pvzI7) as HV50r; move HV50r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV51l; move HV51l before pvzI8; pose proof (proj2 pvzI8) as HV51r; move HV51r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K14l; move K14l before pvzI11; pose proof (proj2 pvzI11) as K14r; move K14r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K21l; move K21l before pvzI12; pose proof (proj2 pvzI12) as K21r; move K21r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K30l; move K30l before pvzI13; pose proof (proj2 pvzI13) as K30r; move K30r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K31l; move K31l before pvzI14; pose proof (proj2 pvzI14) as K31r; move K31r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K40l; move K40l before pvzI15; pose proof (proj2 pvzI15) as K40r; move K40r before pvzI15; clear pvzI15.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 44%nat => Z_to_bv 64 vz_44 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 44%nat => vz_44 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PaenR.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaenR.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaenR.kn0).
  { unfold know_ok, PaenR.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K35) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K35) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K35) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K36) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K36) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K36) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K36) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K36; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K36; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K36; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K36) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K36; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K36; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K36; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K36) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K36; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K36; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K36; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K36) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K36; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K36; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K36; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K36) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K38) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K38) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K38) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K38; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K38; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K38; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K38) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K38) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K38) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K38) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K30l K30r) | exact (conj K30l K30r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K31l K31r K33 K35 K36 K37 K38) | exact (conj K31l K31r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K31l K31r K33 K35 K36 K37 K38) | clear; lia | exact K32]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K31l K31r K33 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K31l K31r K33 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K31l K31r K33 K35 K36 K37 K38; lia | clear - HV36l HV36r K31l K31r K33 K35 K36 K37 K38; lia | clear - HV36l HV36r K31l K31r K33 K35 K36 K37 K38; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K31l K31r K33 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K31l K31r K33 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K31l K31r K33 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K31l K31r K33 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV36l HV36r K31l K31r K33 K35 K36 K37 K38) | evalEk ZA ltac:(clear - HV44l HV44r K40l K40r) | clear - HV36l HV36r K31l K31r K33 K35 K36 K37 K38; lia | clear - HV36l HV36r K31l K31r K33 K35 K36 K37 K38; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV44l HV44r K40l K40r) | exact (conj K40l K40r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaenR.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaenR.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PaenR.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PaenR.ps0) with 0xaf854 in Hms. change (SR.ps_regs PaenR.ps0) with (map (fun i => (i, nth i PaenR.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PaenR.ps0) with PaenR.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PaenR.regs0 PaenR.regs_out0 80 KS_aenR_0 KS_aenR_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PaenR.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaenR.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  - right.
    change (SR.ps_pc PaenR.ps1) with 0xaf70c in Hms. change (SR.ps_regs PaenR.ps1) with (map (fun i => (i, nth i PaenR.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PaenR.ps1) with PaenR.cells1 in Hcells. unfold PaenR.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PaenR.regs0 PaenR.regs_out1 80 KS_aenR_1 KS_aenR_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PaenR.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PaenR.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PaenT := LibSegBa_aenT_b.
Definition KS_aenT : list nat := Eval vm_compute in (BG.kept_list 80 PaenT.regs0 PaenT.regs_out0).
Lemma KS_aenT_ok : BG.kept_ok 80 PaenT.regs0 PaenT.regs_out0 KS_aenT = true. Proof. vm_compute. reflexivity. Qed.
Lemma aenT_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 18) = Z_to_bv 64 (V 50%nat) -> getr R (reg 19) = Z_to_bv 64 (V 33%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 34%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 33%nat) + 344) -> getr R (reg 23) = Z_to_bv 64 (V 35%nat) -> getr R (reg 24) = Z_to_bv 64 (V 50%nat) -> getr R (reg 25) = Z_to_bv 64 2147450880 -> getr R (reg 26) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 ((((V 33%nat) + 344) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 344) / 8) + 2147450880) 3 ->
  L5KA.zeros_at M ((((V 33%nat) + 345) / 8) + 2147450880) 1 -> (((V 2%nat) - 128) + 128 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 128)) -> 6905856 <= (V 50%nat) <= 140737488355264 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 64 -> L5.writable RSEGS M (V 50%nat) 64 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 8 ->
  L5.u64_at RSEGS M ((V 50%nat) + 56) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 64 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 128) + 128 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 128)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 64 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 69%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 72%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 51%nat) + 0) <= bv_unsigned a < ((V 51%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 51%nat) + 0) <= i < ((V 51%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xaf854 M) (st fx' R' 0xaf8f0 M')
        /\ (forall x, In x KS_aenT -> getr R' (reg x) = getr R (reg x))
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
        /\ L5.u8_at RSEGS M' (V 51%nat) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450883) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450882) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450881) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450880) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450887) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450886) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450885) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450884) 245
        /\ L5.u64_at RSEGS M' (V 50%nat) 1172321806
        /\ L5.defined M' ((V 50%nat) + 8) 56).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 pvzI20 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI21 K4 K5 pvzI22 K7 K8 K9 K10 K11 K12 K13 pvzI23 K15 K16 K17 K18 K19 K20 pvzI24 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV50l; move HV50l before pvzI6; pose proof (proj2 pvzI6) as HV50r; move HV50r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV51l; move HV51l before pvzI7; pose proof (proj2 pvzI7) as HV51r; move HV51r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV60l; move HV60l before pvzI8; pose proof (proj2 pvzI8) as HV60r; move HV60r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV61l; move HV61l before pvzI9; pose proof (proj2 pvzI9) as HV61r; move HV61r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV62l; move HV62l before pvzI10; pose proof (proj2 pvzI10) as HV62r; move HV62r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV63l; move HV63l before pvzI11; pose proof (proj2 pvzI11) as HV63r; move HV63r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV64l; move HV64l before pvzI12; pose proof (proj2 pvzI12) as HV64r; move HV64r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV65l; move HV65l before pvzI13; pose proof (proj2 pvzI13) as HV65r; move HV65r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV66l; move HV66l before pvzI14; pose proof (proj2 pvzI14) as HV66r; move HV66r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV67l; move HV67l before pvzI15; pose proof (proj2 pvzI15) as HV67r; move HV67r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV68l; move HV68l before pvzI16; pose proof (proj2 pvzI16) as HV68r; move HV68r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV69l; move HV69l before pvzI17; pose proof (proj2 pvzI17) as HV69r; move HV69r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV70l; move HV70l before pvzI18; pose proof (proj2 pvzI18) as HV70r; move HV70r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV71l; move HV71l before pvzI19; pose proof (proj2 pvzI19) as HV71r; move HV71r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as HV72l; move HV72l before pvzI20; pose proof (proj2 pvzI20) as HV72r; move HV72r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K3l; move K3l before pvzI21; pose proof (proj2 pvzI21) as K3r; move K3r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K6l; move K6l before pvzI22; pose proof (proj2 pvzI22) as K6r; move K6r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K14l; move K14l before pvzI23; pose proof (proj2 pvzI23) as K14r; move K14r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K21l; move K21l before pvzI24; pose proof (proj2 pvzI24) as K21r; move K21r before pvzI24; clear pvzI24.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 73%nat. }
  assert (HR: regs_ok E PaenT.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaenT.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaenT.kn0).
  { unfold know_ok, PaenT.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K21l K21r K23 K24 K26 K28; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV61l HV61r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV63l HV63r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K42]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaenT.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaenT.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 8) -> ~ ((((vz_50 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 0) + 8) -> ~ ((vz_51 + 0) <= bv_unsigned a < (vz_51 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PaenT.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk' ZA Hag ltac:(clear) | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaenT.ps0) with 0xaf8f0 in Hms. change (SR.ps_regs PaenT.ps0) with (map (fun i => (i, nth i PaenT.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaenT.ps0) with PaenT.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaenT.regs0 PaenT.regs_out0 80 KS_aenT KS_aenT_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaenT.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaenT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenT.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaenT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenT.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaenT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenT.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PaenT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenT.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaenT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenT.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaenT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenT.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaenT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenT.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PaenT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenT.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PaenT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenT.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PaenT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenT.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PaenT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenT.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PaenT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenT.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PaenT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenT.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PaenT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenT.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PaenT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PaenVS := LibSegBa_aenVS_b.
Definition KS_aenVS : list nat := Eval vm_compute in (BG.kept_list 80 PaenVS.regs0 PaenVS.regs_out0).
Lemma KS_aenVS_ok : BG.kept_ok 80 PaenVS.regs0 PaenVS.regs_out0 KS_aenVS = true. Proof. vm_compute. reflexivity. Qed.
Lemma aenVS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 18) = Z_to_bv 64 (V 50%nat) -> getr R (reg 19) = Z_to_bv 64 (V 33%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 34%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 33%nat) + 344) -> getr R (reg 23) = Z_to_bv 64 (V 35%nat) -> getr R (reg 24) = Z_to_bv 64 (V 50%nat) -> getr R (reg 25) = Z_to_bv 64 2147450880 -> getr R (reg 26) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 ((((V 33%nat) + 344) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 344) / 8) + 2147450880) 3 ->
  L5KA.zeros_at M ((((V 33%nat) + 345) / 8) + 2147450880) 1 -> (((V 2%nat) - 128) + 128 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 128)) -> 6905856 <= (V 50%nat) <= 140737488355264 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 64 -> L5.writable RSEGS M (V 50%nat) 64 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 8 ->
  L5.u64_at RSEGS M ((V 50%nat) + 56) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 64 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 128) + 128 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 128)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 64 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u8_at RSEGS M ((V 33%nat) + 344) (V 42%nat) -> 0 <= (V 42%nat) <= 255 ->
  Z.testbit (V 42%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xaf70c M) (st fx' R' 0xb2f54 M')
        /\ (forall x, In x KS_aenVS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 718688
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 345)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 42%nat) / 2)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI9 K4 K5 pvzI10 K7 K8 K9 K10 K11 K12 K13 pvzI11 K15 K16 K17 K18 K19 K20 pvzI12 K22 K23 K24 K25 K26 K27 K28 K29 K30 pvzI13 K32.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV42l; move HV42l before pvzI6; pose proof (proj2 pvzI6) as HV42r; move HV42r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV50l; move HV50l before pvzI7; pose proof (proj2 pvzI7) as HV50r; move HV50r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV51l; move HV51l before pvzI8; pose proof (proj2 pvzI8) as HV51r; move HV51r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K14l; move K14l before pvzI11; pose proof (proj2 pvzI11) as K14r; move K14r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K21l; move K21l before pvzI12; pose proof (proj2 pvzI12) as K21r; move K21r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K31l; move K31l before pvzI13; pose proof (proj2 pvzI13) as K31r; move K31r before pvzI13; clear pvzI13.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 42%nat => Z_to_bv 64 vz_42 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 42%nat => vz_42 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PaenVS.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaenVS.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaenVS.kn0).
  { unfold know_ok, PaenVS.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K21l K21r K23 K24 K26 K28; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear - HV42l HV42r K31l K31r K32) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | byte_tac ltac:(clear - HV42l HV42r K31l K31r K32) | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K31l K31r K32) | exact (conj K31l K31r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV42l HV42r K31l K31r K32) | clear; lia | rewrite (L5K.land1_bit0_false vz_42 ltac:(clear - HV42l HV42r K31l K31r K32; lia) K32); clear; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaenVS.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaenVS.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PaenVS.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaenVS.ps0) with 0xb2f54 in Hms. change (SR.ps_regs PaenVS.ps0) with (map (fun i => (i, nth i PaenVS.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaenVS.ps0) with PaenVS.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaenVS.regs0 PaenVS.regs_out0 80 KS_aenVS KS_aenVS_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaenVS.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaenVS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenVS.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaenVS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PaenVS.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaenVS.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PaenVL := LibSegBa_aenVL_b.
Definition KS_aenVL : list nat := Eval vm_compute in (BG.kept_list 80 PaenVL.regs0 PaenVL.regs_out0).
Lemma KS_aenVL_ok : BG.kept_ok 80 PaenVL.regs0 PaenVL.regs_out0 KS_aenVL = true. Proof. vm_compute. reflexivity. Qed.
Lemma aenVL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 18) = Z_to_bv 64 (V 50%nat) -> getr R (reg 19) = Z_to_bv 64 (V 33%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 34%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 33%nat) + 344) -> getr R (reg 23) = Z_to_bv 64 (V 35%nat) -> getr R (reg 24) = Z_to_bv 64 (V 50%nat) -> getr R (reg 25) = Z_to_bv 64 2147450880 -> getr R (reg 26) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 ((((V 33%nat) + 344) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 344) / 8) + 2147450880) 3 ->
  L5KA.zeros_at M ((((V 33%nat) + 345) / 8) + 2147450880) 1 -> (((V 2%nat) - 128) + 128 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 128)) -> 6905856 <= (V 50%nat) <= 140737488355264 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 64 -> L5.writable RSEGS M (V 50%nat) 64 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 8 ->
  L5.u64_at RSEGS M ((V 50%nat) + 56) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 64 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 128) + 128 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 128)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 64 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u8_at RSEGS M ((V 33%nat) + 344) (V 42%nat) -> 0 <= (V 42%nat) <= 255 ->
  Z.testbit (V 42%nat) 0 = true -> L5.u64_at RSEGS M ((V 33%nat) + 360) (V 43%nat) -> 4096 <= (V 43%nat) <= 140737488355296 -> (2147446784 + 17592186048512 <= (V 43%nat) \/ (V 43%nat) + 1 <= 2147446784) ->
  L5KA.zeros_at M (((V 43%nat) / 8) + 2147450880) 1 -> ((((V 43%nat) / 8) + 2147450880) + 1 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 43%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 33%nat) + 352) (V 45%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xaf70c M) (st fx' R' 0xb2f54 M')
        /\ (forall x, In x KS_aenVL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 718688
        /\ getr R' (reg 10) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 45%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI11 K4 K5 pvzI12 K7 K8 K9 K10 K11 K12 K13 pvzI13 K15 K16 K17 K18 K19 K20 pvzI14 K22 K23 K24 K25 K26 K27 K28 K29 K30 pvzI15 K32 K33 pvzI16 K35 K36 K37 K38.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV42l; move HV42l before pvzI6; pose proof (proj2 pvzI6) as HV42r; move HV42r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV43l; move HV43l before pvzI7; pose proof (proj2 pvzI7) as HV43r; move HV43r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV45l; move HV45l before pvzI8; pose proof (proj2 pvzI8) as HV45r; move HV45r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV50l; move HV50l before pvzI9; pose proof (proj2 pvzI9) as HV50r; move HV50r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV51l; move HV51l before pvzI10; pose proof (proj2 pvzI10) as HV51r; move HV51r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K3l; move K3l before pvzI11; pose proof (proj2 pvzI11) as K3r; move K3r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K6l; move K6l before pvzI12; pose proof (proj2 pvzI12) as K6r; move K6r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K14l; move K14l before pvzI13; pose proof (proj2 pvzI13) as K14r; move K14r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K21l; move K21l before pvzI14; pose proof (proj2 pvzI14) as K21r; move K21r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K31l; move K31l before pvzI15; pose proof (proj2 pvzI15) as K31r; move K31r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K34l; move K34l before pvzI16; pose proof (proj2 pvzI16) as K34r; move K34r before pvzI16; clear pvzI16.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 45%nat => Z_to_bv 64 vz_45 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 42%nat => vz_42 | 43%nat => vz_43 | 45%nat => vz_45 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PaenVL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaenVL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaenVL.kn0).
  { unfold know_ok, PaenVL.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K21l K21r K23 K24 K26 K28; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear - HV42l HV42r K31l K31r K32) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | byte_tac ltac:(clear - HV42l HV42r K31l K31r K32) | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K31l K31r K32) | exact (conj K31l K31r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV42l HV42r K31l K31r K32) | clear; lia | rewrite (L5K.land1_bit0_true vz_42 ltac:(clear - HV42l HV42r K31l K31r K32; lia) K32); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear - HV43l HV43r K34l K34r K35 K37) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K34l K34r K35 K37) | exact (conj K34l K34r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV43l HV43r K34l K34r K35 K37) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV43l HV43r K34l K34r K35 K37) | evalEk ZA ltac:(clear) | clear - HV43l HV43r K34l K34r K35 K37; lia | clear - HV43l HV43r K34l K34r K35 K37; lia | clear - HV43l HV43r K34l K34r K35 K37; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV43l HV43r K34l K34r K35 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K38]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaenVL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaenVL.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PaenVL.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaenVL.ps0) with 0xb2f54 in Hms. change (SR.ps_regs PaenVL.ps0) with (map (fun i => (i, nth i PaenVL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaenVL.ps0) with PaenVL.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaenVL.regs0 PaenVL.regs_out0 80 KS_aenVL KS_aenVL_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaenVL.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaenVL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenVL.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaenVL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PaenVL.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaenVL.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PaenC := LibSegBa_aenC_b.
Definition KS_aenC_0 : list nat := Eval vm_compute in (BG.kept_list 80 PaenC.regs0 PaenC.regs_out0).
Lemma KS_aenC_0_ok : BG.kept_ok 80 PaenC.regs0 PaenC.regs_out0 KS_aenC_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_aenC_1 : list nat := Eval vm_compute in (BG.kept_list 80 PaenC.regs0 PaenC.regs_out1).
Lemma KS_aenC_1_ok : BG.kept_ok 80 PaenC.regs0 PaenC.regs_out1 KS_aenC_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma aenC_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 11) = Z_to_bv 64 (V 46%nat) -> getr R (reg 18) = Z_to_bv 64 (V 50%nat) -> getr R (reg 19) = Z_to_bv 64 (V 33%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 34%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 33%nat) + 344) -> getr R (reg 23) = Z_to_bv 64 (V 35%nat) -> getr R (reg 24) = Z_to_bv 64 (V 50%nat) -> getr R (reg 25) = Z_to_bv 64 2147450880 -> getr R (reg 26) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 ((((V 33%nat) + 344) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 344) / 8) + 2147450880) 3 ->
  L5KA.zeros_at M ((((V 33%nat) + 345) / 8) + 2147450880) 1 -> (((V 2%nat) - 128) + 128 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 128)) -> 6905856 <= (V 50%nat) <= 140737488355264 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 64 -> L5.writable RSEGS M (V 50%nat) 64 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 8 ->
  L5.u64_at RSEGS M ((V 50%nat) + 56) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 64 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 128) + 128 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 128)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 64 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 33%nat) / 8) + 2147450880)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xaf760 M) (st fx' R' 0xae848 M')
        /\ (forall x, In x KS_aenC_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 719104
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 3)
      \/ (msteps RSEGS (st fx R 0xaf760 M) (st fx' R' 0xaf768 M')
        /\ (forall x, In x KS_aenC_1 -> getr R' (reg x) = getr R (reg x)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G11 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI9 K4 K5 pvzI10 K7 K8 K9 K10 K11 K12 K13 pvzI11 K15 K16 K17 K18 K19 K20 pvzI12 K22 K23 K24 K25 K26 K27 K28 K29.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV46l; move HV46l before pvzI6; pose proof (proj2 pvzI6) as HV46r; move HV46r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV50l; move HV50l before pvzI7; pose proof (proj2 pvzI7) as HV50r; move HV50r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV51l; move HV51l before pvzI8; pose proof (proj2 pvzI8) as HV51r; move HV51r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K14l; move K14l before pvzI11; pose proof (proj2 pvzI11) as K14r; move K14r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K21l; move K21l before pvzI12; pose proof (proj2 pvzI12) as K21r; move K21r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 46%nat => Z_to_bv 64 vz_46 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 46%nat => vz_46 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PaenC.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaenC.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaenC.kn0).
  { unfold know_ok, PaenC.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K21l K21r K23 K24 K26 K28; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaenC.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaenC.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PaenC.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PaenC.ps0) with 0xae848 in Hms. change (SR.ps_regs PaenC.ps0) with (map (fun i => (i, nth i PaenC.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PaenC.ps0) with PaenC.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PaenC.regs0 PaenC.regs_out0 80 KS_aenC_0 KS_aenC_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PaenC.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaenC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PaenC.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaenC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PaenC.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaenC.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
  - right.
    change (SR.ps_pc PaenC.ps1) with 0xaf768 in Hms. change (SR.ps_regs PaenC.ps1) with (map (fun i => (i, nth i PaenC.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PaenC.ps1) with PaenC.cells1 in Hcells. unfold PaenC.cells1 in Hcells.
    split. { exact Hms. }
    intros j Hj. apply (BG.kept_regs E E' R R' PaenC.regs0 PaenC.regs_out1 80 KS_aenC_1 KS_aenC_1_ok HR Hag Hregs j Hj). 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PaenE := LibSegBa_aenE_b.
Definition KS_aenE : list nat := Eval vm_compute in (BG.kept_list 80 PaenE.regs0 PaenE.regs_out0).
Lemma KS_aenE_ok : BG.kept_ok 80 PaenE.regs0 PaenE.regs_out0 KS_aenE = true. Proof. vm_compute. reflexivity. Qed.
Lemma aenE_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 18) = Z_to_bv 64 (V 50%nat) -> getr R (reg 19) = Z_to_bv 64 (V 33%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 34%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 33%nat) + 344) -> getr R (reg 23) = Z_to_bv 64 (V 35%nat) -> getr R (reg 24) = Z_to_bv 64 (V 50%nat) -> getr R (reg 25) = Z_to_bv 64 2147450880 -> getr R (reg 26) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 ((((V 33%nat) + 344) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 344) / 8) + 2147450880) 3 ->
  L5KA.zeros_at M ((((V 33%nat) + 345) / 8) + 2147450880) 1 -> (((V 2%nat) - 128) + 128 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 128)) -> 6905856 <= (V 50%nat) <= 140737488355264 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 64 -> L5.writable RSEGS M (V 50%nat) 64 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 8 ->
  L5.u64_at RSEGS M ((V 50%nat) + 56) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 64 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 128) + 128 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 128)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 64 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 33%nat) / 8) + 2147450880)) -> L5.writable RSEGS M ((V 33%nat) + 8) 1 -> L5.u64_at RSEGS M ((V 2%nat) - 112) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 71%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 104) (V 72%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 1) -> ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 51%nat) + 0) <= bv_unsigned a < ((V 51%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 1) -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 51%nat) + 0) <= i < ((V 51%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xaf900 M) (st fx' R' 0xaf8f0 M')
        /\ (forall x, In x KS_aenE -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 60%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 61%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 62%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
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
        /\ L5.u8_at RSEGS M' (V 51%nat) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450883) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450882) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450881) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450880) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450887) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450886) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450885) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450884) 245
        /\ L5.u64_at RSEGS M' (V 50%nat) 1172321806
        /\ L5.u8_at RSEGS M' ((V 33%nat) + 8) 0
        /\ L5.defined M' ((V 50%nat) + 8) 56).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 pvzI20 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI21 K4 K5 pvzI22 K7 K8 K9 K10 K11 K12 K13 pvzI23 K15 K16 K17 K18 K19 K20 pvzI24 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV50l; move HV50l before pvzI6; pose proof (proj2 pvzI6) as HV50r; move HV50r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV51l; move HV51l before pvzI7; pose proof (proj2 pvzI7) as HV51r; move HV51r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV60l; move HV60l before pvzI8; pose proof (proj2 pvzI8) as HV60r; move HV60r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV61l; move HV61l before pvzI9; pose proof (proj2 pvzI9) as HV61r; move HV61r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV62l; move HV62l before pvzI10; pose proof (proj2 pvzI10) as HV62r; move HV62r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV63l; move HV63l before pvzI11; pose proof (proj2 pvzI11) as HV63r; move HV63r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV64l; move HV64l before pvzI12; pose proof (proj2 pvzI12) as HV64r; move HV64r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV65l; move HV65l before pvzI13; pose proof (proj2 pvzI13) as HV65r; move HV65r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV66l; move HV66l before pvzI14; pose proof (proj2 pvzI14) as HV66r; move HV66r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV67l; move HV67l before pvzI15; pose proof (proj2 pvzI15) as HV67r; move HV67r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV68l; move HV68l before pvzI16; pose proof (proj2 pvzI16) as HV68r; move HV68r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV69l; move HV69l before pvzI17; pose proof (proj2 pvzI17) as HV69r; move HV69r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV70l; move HV70l before pvzI18; pose proof (proj2 pvzI18) as HV70r; move HV70r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV71l; move HV71l before pvzI19; pose proof (proj2 pvzI19) as HV71r; move HV71r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as HV72l; move HV72l before pvzI20; pose proof (proj2 pvzI20) as HV72r; move HV72r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K3l; move K3l before pvzI21; pose proof (proj2 pvzI21) as K3r; move K3r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K6l; move K6l before pvzI22; pose proof (proj2 pvzI22) as K6r; move K6r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K14l; move K14l before pvzI23; pose proof (proj2 pvzI23) as K14r; move K14r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K21l; move K21l before pvzI24; pose proof (proj2 pvzI24) as K21r; move K21r before pvzI24; clear pvzI24.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 73%nat. }
  assert (HR: regs_ok E PaenE.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaenE.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaenE.kn0).
  { unfold know_ok, PaenE.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K21l K21r K23 K24 K26 K28; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV61l HV61r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV63l HV63r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K44]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaenE.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaenE.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_33 + 8) <= bv_unsigned a < (vz_33 + 8) + 1) -> ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 8) -> ~ ((((vz_50 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 0) + 8) -> ~ ((vz_51 + 0) <= bv_unsigned a < (vz_51 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PaenE.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk' ZA Hag ltac:(clear) | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaenE.ps0) with 0xaf8f0 in Hms. change (SR.ps_regs PaenE.ps0) with (map (fun i => (i, nth i PaenE.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaenE.ps0) with PaenE.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaenE.regs0 PaenE.regs_out0 80 KS_aenE KS_aenE_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaenE.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaenE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenE.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaenE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenE.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaenE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenE.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PaenE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenE.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaenE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenE.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaenE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenE.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaenE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenE.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaenE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenE.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PaenE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenE.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PaenE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenE.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PaenE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenE.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PaenE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenE.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PaenE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenE.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PaenE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenE.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PaenE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenE.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PaenE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PaenKS := LibSegBa_aenKS_b.
Definition KS_aenKS : list nat := Eval vm_compute in (BG.kept_list 80 PaenKS.regs0 PaenKS.regs_out0).
Lemma KS_aenKS_ok : BG.kept_ok 80 PaenKS.regs0 PaenKS.regs_out0 KS_aenKS = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma aenKS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 18) = Z_to_bv 64 (V 50%nat) -> getr R (reg 19) = Z_to_bv 64 (V 33%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 34%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 33%nat) + 344) -> getr R (reg 23) = Z_to_bv 64 (V 35%nat) -> getr R (reg 24) = Z_to_bv 64 (V 50%nat) -> getr R (reg 25) = Z_to_bv 64 2147450880 -> getr R (reg 26) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 ((((V 33%nat) + 344) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 344) / 8) + 2147450880) 3 ->
  L5KA.zeros_at M ((((V 33%nat) + 345) / 8) + 2147450880) 1 -> (((V 2%nat) - 128) + 128 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 128)) -> 6905856 <= (V 50%nat) <= 140737488355264 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 64 -> L5.writable RSEGS M (V 50%nat) 64 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 8 ->
  L5.u64_at RSEGS M ((V 50%nat) + 56) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 64 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 128) + 128 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 128)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 64 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u8_at RSEGS M ((V 33%nat) + 344) (V 42%nat) -> 0 <= (V 42%nat) <= 255 ->
  Z.testbit (V 42%nat) 0 = false -> L5.writable RSEGS M ((V 33%nat) + 8) 1 -> L5.u8_at RSEGS M ((V 33%nat) + 10) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 112) (V 50%nat) ->
  6905856 <= (V 34%nat) <= 140737488355320 -> aligned (V 34%nat) 8 -> (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 ->
  (((V 2%nat) - 128) + 128 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 2%nat) - 128)) -> ((V 33%nat) + 416 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 33%nat)) -> ((V 50%nat) + 64 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 50%nat)) -> ((V 51%nat) + 1 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 51%nat)) ->
  L5.u64_at RSEGS M (V 34%nat) 1251456 -> L5KA.zeros_at M 2147607324 1 -> ((((V 34%nat) / 8) + 2147450880) + 1 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 34%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 72%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 50%nat) + 32) <= bv_unsigned a < ((V 50%nat) + 32) + 16) -> ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 1) -> ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 8) -> ~ (((V 51%nat) + 0) <= bv_unsigned a < ((V 51%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 50%nat) + 32) <= i < ((V 50%nat) + 32) + 16) -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 1) -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 8) -> ~ (((V 51%nat) + 0) <= i < ((V 51%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xaf768 M) (st fx' R' 0xaf8f0 M')
        /\ (forall x, In x KS_aenKS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 60%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 61%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 62%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 692892
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
        /\ L5.u8_at RSEGS M' (V 51%nat) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450883) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450882) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450881) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450880) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450887) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450886) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450885) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450884) 245
        /\ L5.u64_at RSEGS M' (V 50%nat) 1172321806
        /\ L5.u8_at RSEGS M' ((V 33%nat) + 8) 1
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 40) ((V 42%nat) / 2)
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 32) ((V 33%nat) + 345)
        /\ L5.defined M' ((V 50%nat) + 8) 24
        /\ L5.defined M' ((V 50%nat) + 48) 16).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 pvzI20 pvzI21 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI22 K4 K5 pvzI23 K7 K8 K9 K10 K11 K12 K13 pvzI24 K15 K16 K17 K18 K19 K20 pvzI25 K22 K23 K24 K25 K26 K27 K28 K29 K30 pvzI26 K32 K33 K34 K35 pvzI27 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57 K58 K59.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV42l; move HV42l before pvzI6; pose proof (proj2 pvzI6) as HV42r; move HV42r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV50l; move HV50l before pvzI7; pose proof (proj2 pvzI7) as HV50r; move HV50r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV51l; move HV51l before pvzI8; pose proof (proj2 pvzI8) as HV51r; move HV51r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV60l; move HV60l before pvzI9; pose proof (proj2 pvzI9) as HV60r; move HV60r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV61l; move HV61l before pvzI10; pose proof (proj2 pvzI10) as HV61r; move HV61r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV62l; move HV62l before pvzI11; pose proof (proj2 pvzI11) as HV62r; move HV62r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV63l; move HV63l before pvzI12; pose proof (proj2 pvzI12) as HV63r; move HV63r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV64l; move HV64l before pvzI13; pose proof (proj2 pvzI13) as HV64r; move HV64r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV65l; move HV65l before pvzI14; pose proof (proj2 pvzI14) as HV65r; move HV65r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV66l; move HV66l before pvzI15; pose proof (proj2 pvzI15) as HV66r; move HV66r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV67l; move HV67l before pvzI16; pose proof (proj2 pvzI16) as HV67r; move HV67r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV68l; move HV68l before pvzI17; pose proof (proj2 pvzI17) as HV68r; move HV68r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV69l; move HV69l before pvzI18; pose proof (proj2 pvzI18) as HV69r; move HV69r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV70l; move HV70l before pvzI19; pose proof (proj2 pvzI19) as HV70r; move HV70r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as HV71l; move HV71l before pvzI20; pose proof (proj2 pvzI20) as HV71r; move HV71r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as HV72l; move HV72l before pvzI21; pose proof (proj2 pvzI21) as HV72r; move HV72r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K3l; move K3l before pvzI22; pose proof (proj2 pvzI22) as K3r; move K3r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K6l; move K6l before pvzI23; pose proof (proj2 pvzI23) as K6r; move K6r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K14l; move K14l before pvzI24; pose proof (proj2 pvzI24) as K14r; move K14r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K21l; move K21l before pvzI25; pose proof (proj2 pvzI25) as K21r; move K21r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K31l; move K31l before pvzI26; pose proof (proj2 pvzI26) as K31r; move K31r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as K36l; move K36l before pvzI27; pose proof (proj2 pvzI27) as K36r; move K36r before pvzI27; clear pvzI27.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 42%nat => Z_to_bv 64 vz_42 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 42%nat => vz_42 | 50%nat => vz_50 | 51%nat => vz_51 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 73%nat. }
  assert (HR: regs_ok E PaenKS.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaenKS.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaenKS.kn0).
  { unfold know_ok, PaenKS.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K40) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K40) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K40) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K40; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K40; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K40; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K41) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K41) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K41) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K41) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K41; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K41; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K41; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K41) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K41; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K41; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K41; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K41) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K41; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K41; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K41; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K41) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K41; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K41; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K41; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K41) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K42 K46) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K42 K46) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K42 K46) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K42 K46; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K42 K46; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K42 K46; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K42 K46) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K42 K46; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K42 K46; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K42 K46; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K42 K46) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K42 K46) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K42 K46; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K42 K46; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K42 K46; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K42 K46) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K43) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K42 K46; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K42 K46; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K43) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K43) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K43; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K43; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K43; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K43) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K42 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K43) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K42 K46) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K43) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K41) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K42 K46) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K41) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K43) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K41) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K42 K46) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K41) | evalEk ZA ltac:(clear - HV42l HV42r K31l K31r K32) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K41; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K41; lia | byte_tac ltac:(clear - HV42l HV42r K31l K31r K32) | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K31l K31r K32) | exact (conj K31l K31r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV42l HV42r K31l K31r K32) | clear; lia | rewrite (L5K.land1_bit0_false vz_42 ltac:(clear - HV42l HV42r K31l K31r K32; lia) K32); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K41) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K41; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K41; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K41; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K41) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K41; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K41; lia | byte_tac ltac:(clear) | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K40) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K42 K46) | clear - HV2l HV2r K3l K3r K13 K25 K26 K40; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K40; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K36l K36r K38 K40 K41 K42 K43 K46) | exact (conj K36l K36r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K36l K36r K38 K40 K41 K42 K43 K46) | clear; lia | exact K37]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K36l K36r K38 K40 K41 K42 K43 K46) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K36l K36r K38 K40 K41 K42 K43 K46) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K36l K36r K38 K40 K41 K42 K43 K46; lia | clear - HV34l HV34r K36l K36r K38 K40 K41 K42 K43 K46; lia | clear - HV34l HV34r K36l K36r K38 K40 K41 K42 K43 K46; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K36l K36r K38 K40 K41 K42 K43 K46) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K41) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K36l K36r K38 K40 K41 K42 K43 K46) | evalEk ZA ltac:(clear) | generalize K41; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K42 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K36l K36r K38 K40 K41 K42 K43 K46) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K43) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K36l K36r K38 K40 K41 K42 K43 K46) | evalEk ZA ltac:(clear) | generalize K43; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K36l K36r K38 K40 K41 K42 K43 K46) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K36l K36r K38 K40 K41 K42 K43 K46; lia | clear - HV34l HV34r K36l K36r K38 K40 K41 K42 K43 K46; lia | exactA K44]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K36l K36r K38 K40 K41 K42 K43 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K42 K46) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K40) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K40; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K40; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K40) | evalEk ZA ltac:(clear - HV61l HV61r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K40; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K40; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K40) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K40; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K40; lia | exactA K49]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K40) | evalEk ZA ltac:(clear - HV63l HV63r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K40; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K40; lia | exactA K50]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K40) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K40; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K40; lia | exactA K51]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K40) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K40; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K40; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K40) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K40; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K40; lia | exactA K53]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K40) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K40; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K40; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K40) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K40; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K40; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K40) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K40; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K40; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K40) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K40; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K40; lia | exactA K57]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K40) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K40; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K40; lia | exactA K58]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K40) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K40; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K40; lia | exactA K59]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaenKS.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaenKS.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((vz_50 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 0) + 8) -> ~ ((vz_50 + 32) <= bv_unsigned a < (vz_50 + 32) + 16) -> ~ ((vz_33 + 8) <= bv_unsigned a < (vz_33 + 8) + 1) -> ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 8) -> ~ ((vz_51 + 0) <= bv_unsigned a < (vz_51 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3 Hn4. apply Hfr. unfold PaenKS.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K42 K46) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K42 K46 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K42 K46) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K42 K46 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K41) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K41 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K42 K46) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K42 K46 Hn3; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K43) | evalEk' ZA Hag ltac:(clear) | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K43 Hn4; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3 Hn4. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaenKS.ps0) with 0xaf8f0 in Hms. change (SR.ps_regs PaenKS.ps0) with (map (fun i => (i, nth i PaenKS.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaenKS.ps0) with PaenKS.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaenKS.regs0 PaenKS.regs_out0 80 KS_aenKS KS_aenKS_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaenKS.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaenKS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenKS.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaenKS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenKS.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaenKS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenKS.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PaenKS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenKS.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaenKS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenKS.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaenKS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenKS.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PaenKS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenKS.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PaenKS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenKS.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PaenKS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenKS.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaenKS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenKS.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaenKS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenKS.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PaenKS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenKS.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PaenKS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenKS.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PaenKS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenKS.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PaenKS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenKS.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PaenKS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenKS.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PaenKS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenKS.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PaenKS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenKS.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PaenKS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K43) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K42 K46) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K42 K46) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K42 K46) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K42 K46) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K42 K46) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K42 K46) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K42 K46) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K42 K46) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K42 K46) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K41) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K42 K46) | evalEk' ZA Hag ltac:(clear - HV42l HV42r K31l K31r K32) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K42 K46) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K41) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K42 K46) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K42 K46) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PaenKL := LibSegBa_aenKL_b.
Definition KS_aenKL : list nat := Eval vm_compute in (BG.kept_list 80 PaenKL.regs0 PaenKL.regs_out0).
Lemma KS_aenKL_ok : BG.kept_ok 80 PaenKL.regs0 PaenKL.regs_out0 KS_aenKL = true. Proof. vm_compute. reflexivity. Qed.
Lemma aenKL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 18) = Z_to_bv 64 (V 50%nat) -> getr R (reg 19) = Z_to_bv 64 (V 33%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 34%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 33%nat) + 344) -> getr R (reg 23) = Z_to_bv 64 (V 35%nat) -> getr R (reg 24) = Z_to_bv 64 (V 50%nat) -> getr R (reg 25) = Z_to_bv 64 2147450880 -> getr R (reg 26) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 ((((V 33%nat) + 344) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 344) / 8) + 2147450880) 3 ->
  L5KA.zeros_at M ((((V 33%nat) + 345) / 8) + 2147450880) 1 -> (((V 2%nat) - 128) + 128 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 128)) -> 6905856 <= (V 50%nat) <= 140737488355264 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 64 -> L5.writable RSEGS M (V 50%nat) 64 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 8 ->
  L5.u64_at RSEGS M ((V 50%nat) + 56) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 64 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 128) + 128 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 128)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 64 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u8_at RSEGS M ((V 33%nat) + 344) (V 42%nat) -> 0 <= (V 42%nat) <= 255 ->
  Z.testbit (V 42%nat) 0 = true -> L5.u64_at RSEGS M ((V 33%nat) + 360) (V 43%nat) -> 4096 <= (V 43%nat) <= 140737488355296 -> (2147446784 + 17592186048512 <= (V 43%nat) \/ (V 43%nat) + 1 <= 2147446784) ->
  L5KA.zeros_at M (((V 43%nat) / 8) + 2147450880) 1 -> ((((V 43%nat) / 8) + 2147450880) + 1 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 43%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 33%nat) + 352) (V 45%nat) -> L5.writable RSEGS M ((V 33%nat) + 8) 1 ->
  L5.u8_at RSEGS M ((V 33%nat) + 10) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 112) (V 50%nat) -> 6905856 <= (V 34%nat) <= 140737488355320 -> aligned (V 34%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 -> (((V 2%nat) - 128) + 128 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 2%nat) - 128)) -> ((V 33%nat) + 416 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 33%nat)) ->
  ((V 50%nat) + 64 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 50%nat)) -> ((V 51%nat) + 1 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 51%nat)) -> L5.u64_at RSEGS M (V 34%nat) 1251456 -> L5KA.zeros_at M 2147607324 1 ->
  ((((V 34%nat) / 8) + 2147450880) + 1 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 34%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 70%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 96) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 72%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 50%nat) + 32) <= bv_unsigned a < ((V 50%nat) + 32) + 16) -> ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 1) -> ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 8) -> ~ (((V 51%nat) + 0) <= bv_unsigned a < ((V 51%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 50%nat) + 32) <= i < ((V 50%nat) + 32) + 16) -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 1) -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 8) -> ~ (((V 51%nat) + 0) <= i < ((V 51%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xaf768 M) (st fx' R' 0xaf8f0 M')
        /\ (forall x, In x KS_aenKL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 60%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 61%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 62%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 692892
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
        /\ L5.u8_at RSEGS M' (V 51%nat) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450883) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450882) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450881) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450880) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450887) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450886) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450885) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450884) 245
        /\ L5.u64_at RSEGS M' (V 50%nat) 1172321806
        /\ L5.u8_at RSEGS M' ((V 33%nat) + 8) 1
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 40) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 32) (V 43%nat)
        /\ L5.defined M' ((V 50%nat) + 8) 24
        /\ L5.defined M' ((V 50%nat) + 48) 16).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 pvzI20 pvzI21 pvzI22 pvzI23 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI24 K4 K5 pvzI25 K7 K8 K9 K10 K11 K12 K13 pvzI26 K15 K16 K17 K18 K19 K20 pvzI27 K22 K23 K24 K25 K26 K27 K28 K29 K30 pvzI28 K32 K33 pvzI29 K35 K36 K37 K38 K39 K40 K41 pvzI30 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57 K58 K59 K60 K61 K62 K63 K64 K65.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV42l; move HV42l before pvzI6; pose proof (proj2 pvzI6) as HV42r; move HV42r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV43l; move HV43l before pvzI7; pose proof (proj2 pvzI7) as HV43r; move HV43r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV45l; move HV45l before pvzI8; pose proof (proj2 pvzI8) as HV45r; move HV45r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV50l; move HV50l before pvzI9; pose proof (proj2 pvzI9) as HV50r; move HV50r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV51l; move HV51l before pvzI10; pose proof (proj2 pvzI10) as HV51r; move HV51r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV60l; move HV60l before pvzI11; pose proof (proj2 pvzI11) as HV60r; move HV60r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV61l; move HV61l before pvzI12; pose proof (proj2 pvzI12) as HV61r; move HV61r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV62l; move HV62l before pvzI13; pose proof (proj2 pvzI13) as HV62r; move HV62r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV63l; move HV63l before pvzI14; pose proof (proj2 pvzI14) as HV63r; move HV63r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV64l; move HV64l before pvzI15; pose proof (proj2 pvzI15) as HV64r; move HV64r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV65l; move HV65l before pvzI16; pose proof (proj2 pvzI16) as HV65r; move HV65r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV66l; move HV66l before pvzI17; pose proof (proj2 pvzI17) as HV66r; move HV66r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV67l; move HV67l before pvzI18; pose proof (proj2 pvzI18) as HV67r; move HV67r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV68l; move HV68l before pvzI19; pose proof (proj2 pvzI19) as HV68r; move HV68r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as HV69l; move HV69l before pvzI20; pose proof (proj2 pvzI20) as HV69r; move HV69r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as HV70l; move HV70l before pvzI21; pose proof (proj2 pvzI21) as HV70r; move HV70r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as HV71l; move HV71l before pvzI22; pose proof (proj2 pvzI22) as HV71r; move HV71r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as HV72l; move HV72l before pvzI23; pose proof (proj2 pvzI23) as HV72r; move HV72r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K3l; move K3l before pvzI24; pose proof (proj2 pvzI24) as K3r; move K3r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K6l; move K6l before pvzI25; pose proof (proj2 pvzI25) as K6r; move K6r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K14l; move K14l before pvzI26; pose proof (proj2 pvzI26) as K14r; move K14r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as K21l; move K21l before pvzI27; pose proof (proj2 pvzI27) as K21r; move K21r before pvzI27; clear pvzI27. pose proof (proj1 pvzI28) as K31l; move K31l before pvzI28; pose proof (proj2 pvzI28) as K31r; move K31r before pvzI28; clear pvzI28. pose proof (proj1 pvzI29) as K34l; move K34l before pvzI29; pose proof (proj2 pvzI29) as K34r; move K34r before pvzI29; clear pvzI29. pose proof (proj1 pvzI30) as K42l; move K42l before pvzI30; pose proof (proj2 pvzI30) as K42r; move K42r before pvzI30; clear pvzI30.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 45%nat => Z_to_bv 64 vz_45 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 42%nat => vz_42 | 43%nat => vz_43 | 45%nat => vz_45 | 50%nat => vz_50 | 51%nat => vz_51 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 73%nat. }
  assert (HR: regs_ok E PaenKL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PaenKL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PaenKL.kn0).
  { unfold know_ok, PaenKL.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K48 K52) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K48 K52) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K48 K52) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K48 K52; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K48 K52; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K48 K52; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K48 K52) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K48 K52; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K48 K52; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K48 K52; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K48 K52) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K48 K52) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K48 K52; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K48 K52; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K48 K52; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K48 K52) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K48 K52; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K48 K52; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K48 K52) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K48 K52) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K48 K52) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K48 K52) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | evalEk ZA ltac:(clear - HV42l HV42r K31l K31r K32) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47; lia | byte_tac ltac:(clear - HV42l HV42r K31l K31r K32) | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K31l K31r K32) | exact (conj K31l K31r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV42l HV42r K31l K31r K32) | clear; lia | rewrite (L5K.land1_bit0_true vz_42 ltac:(clear - HV42l HV42r K31l K31r K32; lia) K32); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | evalEk ZA ltac:(clear - HV43l HV43r K34l K34r K35 K37) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K34l K34r K35 K37) | exact (conj K34l K34r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV43l HV43r K34l K34r K35 K37) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV43l HV43r K34l K34r K35 K37) | evalEk ZA ltac:(clear) | clear - HV43l HV43r K34l K34r K35 K37; lia | clear - HV43l HV43r K34l K34r K35 K37; lia | clear - HV43l HV43r K34l K34r K35 K37; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV43l HV43r K34l K34r K35 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K48 K52) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47; lia | byte_tac ltac:(clear) | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K48 K52) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K42l K42r K44 K46 K47 K48 K49 K52) | exact (conj K42l K42r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K42l K42r K44 K46 K47 K48 K49 K52) | clear; lia | exact K43]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K42l K42r K44 K46 K47 K48 K49 K52) | evalEk ZA ltac:(clear) | generalize K44; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K42l K42r K44 K46 K47 K48 K49 K52) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K42l K42r K44 K46 K47 K48 K49 K52; lia | clear - HV34l HV34r K42l K42r K44 K46 K47 K48 K49 K52; lia | clear - HV34l HV34r K42l K42r K44 K46 K47 K48 K49 K52; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K42l K42r K44 K46 K47 K48 K49 K52) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K42l K42r K44 K46 K47 K48 K49 K52) | evalEk ZA ltac:(clear) | generalize K47; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K48 K52) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K42l K42r K44 K46 K47 K48 K49 K52) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K42l K42r K44 K46 K47 K48 K49 K52) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K42l K42r K44 K46 K47 K48 K49 K52) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K42l K42r K44 K46 K47 K48 K49 K52; lia | clear - HV34l HV34r K42l K42r K44 K46 K47 K48 K49 K52; lia | exactA K50]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K51]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K42l K42r K44 K46 K47 K48 K49 K52) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K48 K52) | evalEk ZA ltac:(clear) | generalize K52; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K53]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV61l HV61r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV63l HV63r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K57]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K58]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K59]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K60]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K61]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K62]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K63]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K64]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K65]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PaenKL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PaenKL.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((vz_50 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 0) + 8) -> ~ ((vz_50 + 32) <= bv_unsigned a < (vz_50 + 32) + 16) -> ~ ((vz_33 + 8) <= bv_unsigned a < (vz_33 + 8) + 1) -> ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 8) -> ~ ((vz_51 + 0) <= bv_unsigned a < (vz_51 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3 Hn4. apply Hfr. unfold PaenKL.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K48 K52) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K48 K52 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K48 K52) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K48 K52 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K48 K52) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K48 K52 Hn3; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | evalEk' ZA Hag ltac:(clear) | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49 Hn4; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3 Hn4. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PaenKL.ps0) with 0xaf8f0 in Hms. change (SR.ps_regs PaenKL.ps0) with (map (fun i => (i, nth i PaenKL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PaenKL.ps0) with PaenKL.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PaenKL.regs0 PaenKL.regs_out0 80 KS_aenKL KS_aenKL_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PaenKL.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PaenKL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenKL.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PaenKL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenKL.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PaenKL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenKL.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PaenKL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenKL.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PaenKL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenKL.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PaenKL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenKL.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PaenKL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenKL.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PaenKL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenKL.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PaenKL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenKL.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PaenKL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenKL.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PaenKL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenKL.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PaenKL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenKL.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PaenKL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenKL.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PaenKL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenKL.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PaenKL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenKL.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PaenKL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenKL.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PaenKL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenKL.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PaenKL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PaenKL.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PaenKL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K48 K52) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K48 K52) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K48 K52) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K48 K52) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K48 K52) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K48 K52) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K48 K52) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K48 K52) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K48 K52) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K48 K52) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K48 K52) | evalEk' ZA Hag ltac:(clear - HV43l HV43r K34l K34r K35 K37) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K48 K52) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37 K48 K52) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

End PNAENP.
